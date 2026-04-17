# Checking mode (§7.4) and motive checking (§7.3).
#
# `check : Ctx → Tm → Val → Computation Tm` verifies that `tm` has type
# `ty` and returns an elaborated term. The dispatch handles introduction
# forms against their corresponding type formers (Lam/Pi, Pair/Sigma,
# Zero/Nat, etc.) and falls through to synthesis for anything not
# matched, using `conv` to compare the inferred type against the
# expected one (sub rule, with cumulativity for universes).
#
# `checkMotive` enforces that a motive has type `domTy → U(k)` for some
# `k`, enabling large elimination. Lambda motives extend the context
# with `domTy` and `checkType` on the body; non-lambda motives infer a
# type and validate the shape.
#
# The Succ and Cons branches trampoline over `builtins.genericClosure`
# to handle deep chains without stack pressure (§11.3). The `desc-con`
# branch peels homogeneous recursive-data chains along their single
# recursive position when `linearProfile` of the outer description's
# false-branch exposes a list of field types.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  C = fx.tc.conv;

  K = fx.kernel;
  pure = K.pure;
  send = K.send;
  bind = K.bind;

  typeError = msg: expected: got: term:
    send "typeError" { inherit msg expected got term; };
in {
  scope = {
    checkMotive = ctx: motTm: domTy:
      if motTm.tag == "lam" then
        let ctx' = self.extend ctx motTm.name domTy;
        in bind (self.checkType ctx' motTm.body) (bodyTm:
          pure (T.mkLam motTm.name (Q.quote ctx.depth domTy) bodyTm))
      else
        bind (self.infer ctx motTm) (result:
          let rTy = result.type; in
          if rTy.tag != "VPi"
          then typeError "eliminator motive must be a function"
            { tag = "pi"; } (Q.quote ctx.depth rTy) motTm
          else if !(C.conv ctx.depth rTy.domain domTy)
          then typeError "eliminator motive domain mismatch"
            (Q.quote ctx.depth domTy) (Q.quote ctx.depth rTy.domain) motTm
          else
            let codVal = E.instantiate rTy.closure (V.freshVar ctx.depth); in
            if codVal.tag != "VU"
            then typeError "eliminator motive must return a type"
              { tag = "U"; } (Q.quote ctx.depth codVal) motTm
            else pure result.term);

    check = ctx: tm: ty:
      let t = tm.tag; in

      if t == "lam" && ty.tag == "VPi" then
        let
          dom = ty.domain;
          cod = E.instantiate ty.closure (V.freshVar ctx.depth);
          ctx' = self.extend ctx tm.name dom;
        in bind (self.check ctx' tm.body cod) (body':
          pure (T.mkLam tm.name (Q.quote ctx.depth dom) body'))

      else if t == "pair" && ty.tag == "VSigma" then
        let fstTy = ty.fst; in
        bind (self.check ctx tm.fst fstTy) (a':
          let bTy = E.instantiate ty.closure (E.eval ctx.env a'); in
          bind (self.check ctx tm.snd bTy) (b':
            pure (T.mkPair a' b')))

      else if t == "zero" && ty.tag == "VNat" then pure T.mkZero

      # Succ trampolined for large naturals (S^10000+): peel Succ layers,
      # check the base once, fold mkSucc back.
      else if t == "succ" && ty.tag == "VNat" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "succ"
              then [{ key = item.key + 1; val = item.val.pred; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in bind (self.check ctx base V.vNat) (base':
          pure (builtins.foldl' (acc: _: T.mkSucc acc) base' (builtins.genList (x: x) n)))

      else if t == "true" && ty.tag == "VBool" then pure T.mkTrue
      else if t == "false" && ty.tag == "VBool" then pure T.mkFalse

      else if t == "nil" && ty.tag == "VList" then
        pure (T.mkNil (Q.quote ctx.depth ty.elem))

      # Cons trampolined for deep lists (5000+ elements).
      else if t == "cons" && ty.tag == "VList" then
        let
          elemTy = ty.elem;
          elemTm = Q.quote ctx.depth elemTy;
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "cons"
              then [{ key = item.key + 1; val = item.val.tail; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in bind (self.check ctx base ty) (baseTm:
          builtins.foldl' (accComp: i:
            let node = (builtins.elemAt chain (n - 1 - i)).val; in
            bind accComp (acc:
              bind (self.check ctx node.head elemTy) (h':
                pure (T.mkCons elemTm h' acc)))
          ) (pure baseTm) (builtins.genList (x: x) n))

      else if t == "tt" && ty.tag == "VUnit" then pure T.mkTt

      else if t == "inl" && ty.tag == "VSum" then
        bind (self.check ctx tm.term ty.left) (v':
          pure (T.mkInl (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

      else if t == "inr" && ty.tag == "VSum" then
        bind (self.check ctx tm.term ty.right) (v':
          pure (T.mkInr (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

      # Refl checked against Eq — verify lhs ≡ rhs.
      else if t == "refl" && ty.tag == "VEq" then
        if C.conv ctx.depth ty.lhs ty.rhs
        then pure T.mkRefl
        else typeError "refl requires equal sides"
          (Q.quote ctx.depth ty.lhs) (Q.quote ctx.depth ty.rhs) tm

      else if t == "let" then
        bind (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
          bind (self.check ctx tm.val aVal) (tTm:
            let
              tVal = E.eval ctx.env tTm;
              ctx' = {
                env = [ tVal ] ++ ctx.env;
                types = [ aVal ] ++ ctx.types;
                depth = ctx.depth + 1;
              };
            in bind (self.check ctx' tm.body ty) (uTm:
              pure (T.mkLet tm.name aTm tTm uTm))))

      else if t == "string-lit" && ty.tag == "VString" then pure (T.mkStringLit tm.value)
      else if t == "int-lit" && ty.tag == "VInt" then pure (T.mkIntLit tm.value)
      else if t == "float-lit" && ty.tag == "VFloat" then pure (T.mkFloatLit tm.value)
      else if t == "attrs-lit" && ty.tag == "VAttrs" then pure T.mkAttrsLit
      else if t == "path-lit" && ty.tag == "VPath" then pure T.mkPathLit
      else if t == "fn-lit" && ty.tag == "VFunction" then pure T.mkFnLit
      else if t == "any-lit" && ty.tag == "VAny" then pure T.mkAnyLit

      # Opaque lambda checked against Pi: verify domain conv-equality.
      else if t == "opaque-lam" && ty.tag == "VPi" then
        bind (self.checkType ctx tm.piTy) (piTyTm:
          let piTyVal = E.eval ctx.env piTyTm; in
          if piTyVal.tag != "VPi" then
            typeError "opaque-lam annotation must be Pi"
              (Q.quote ctx.depth ty) (Q.quote ctx.depth piTyVal) tm
          else if !(C.conv ctx.depth piTyVal.domain ty.domain) then
            typeError "opaque-lam domain mismatch"
              (Q.quote ctx.depth ty.domain) (Q.quote ctx.depth piTyVal.domain) tm
          else pure (T.mkOpaqueLam tm._fnBox piTyTm))

      # desc-con checked against Mu — trampolined for deep recursive data
      # (5000+). Peels a homogeneous desc-con chain along its single
      # recursive position. The outer D's false-branch shape drives
      # decomposition: iff `linearProfile subFalse` is a list of n data-
      # field types, each layer's payload is
      # `pair false (pair f_1 (… (pair REC tt) …))` with n heads and a
      # rec tail. Non-linear shapes (tree, mutual recursion) fall through
      # to per-layer checking.
      #
      # D-sharing across layers: fast path is structural equality of the
      # D subterm (holds when elaborate emits a shared dTm per chain);
      # fallback is conv-equality of the evaluated D against the outer
      # dVal.
      else if t == "desc-con" && ty.tag == "VMu" then
        bind (self.check ctx tm.D V.vDesc) (dTm:
          let dVal = E.eval ctx.env dTm; in
          if !(C.conv ctx.depth dVal ty.D)
          then typeError "desc-con description mismatch"
            (Q.quote ctx.depth ty.D) (Q.quote ctx.depth dVal) tm
          else
            let
              subFalse =
                if ty.D.tag != "VDescArg" then null
                else E.instantiate ty.D.T V.vFalse;
              profile = if subFalse == null then null else E.linearProfile subFalse;
              nFields = if profile == null then 0 else builtins.length profile;
              sameD = d2Tm:
                if d2Tm == tm.D then true
                else C.conv ctx.depth (E.eval ctx.env d2Tm) dVal;
              walkPayload = payload:
                if payload.tag != "pair" then null
                else if payload.fst.tag != "false" then null
                else
                  let
                    collect = i: p: acc:
                      if i == nFields then
                        if p.tag != "pair" then null
                        else if p.snd.tag != "tt" then null
                        else if p.fst.tag != "desc-con" then null
                        else { heads = acc; tail = p.fst; }
                      else
                        if p.tag != "pair" then null
                        else collect (i + 1) p.snd (acc ++ [p.fst]);
                  in collect 0 payload.snd [];
              peel = node:
                if profile == null then null
                else if node.tag != "desc-con" then null
                else if !(sameD node.D) then null
                else walkPayload node.d;
              # Integer key is sufficient for genericClosure dedup. `peel` is
              # O(1) field inspection returning a reference to an existing
              # sub-Tm of the concrete `tm`; no deferred continuation work
              # accumulates across steps, so the deepSeq-in-key defensive
              # pattern from fx/trampoline.nix is not needed here and would
              # add O(N²) cost.
              chain = builtins.genericClosure {
                startSet = [{ key = 0; val = tm; }];
                operator = item:
                  let peeled = peel item.val; in
                  if peeled == null then []
                  else [{ key = item.key + 1; val = peeled.tail; }];
              };
              n = builtins.length chain - 1;
              base = (builtins.elemAt chain n).val;
              interpTy = E.interp ty.D (V.vMu ty.D);
            in bind (self.check ctx base.d interpTy) (baseDataTm:
              let baseTm = T.mkDescCon dTm baseDataTm; in
              builtins.foldl' (accComp: i:
                let
                  layer = (builtins.elemAt chain (n - 1 - i)).val;
                  peeled = peel layer;
                  heads = peeled.heads;
                  checkHeads = remaining: accTms:
                    if remaining == [] then pure accTms
                    else
                      let
                        h = builtins.head remaining;
                        rest = builtins.tail remaining;
                      in bind (self.check ctx h.head h.S) (hTm:
                        checkHeads rest (accTms ++ [hTm]));
                  tasks = builtins.genList (j:
                    { head = builtins.elemAt heads j;
                      S = (builtins.elemAt profile j).S;
                    }) nFields;
                  buildInner = hTms: innerTail:
                    if hTms == [] then innerTail
                    else T.mkPair (builtins.head hTms)
                                  (buildInner (builtins.tail hTms) innerTail);
                in bind accComp (acc:
                  bind (checkHeads tasks []) (hTms:
                    pure (T.mkDescCon dTm
                      (T.mkPair T.mkFalse
                        (buildInner hTms (T.mkPair acc T.mkTt))))))
              ) (pure baseTm) (builtins.genList (x: x) n)))

      # Sub rule (§7.4): fall through to synthesis, with cumulativity
      # for universes (§8.3: VU(i) ≤ VU(j) when i ≤ j).
      else
        bind (self.infer ctx tm) (result:
          let inferredTy = result.type; in
          if inferredTy.tag == "VU" && ty.tag == "VU" && inferredTy.level <= ty.level
          then pure result.term
          else if C.conv ctx.depth inferredTy ty
          then pure result.term
          else typeError "type mismatch"
            (Q.quote ctx.depth ty) (Q.quote ctx.depth inferredTy) tm);
  };
  tests = {};
}
