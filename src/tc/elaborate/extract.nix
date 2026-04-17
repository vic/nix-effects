# Elaboration: kernel → Nix value extraction.
#
# `extractInner` is the reverse direction of `elaborateValue`: given an HOAS
# type, a kernel type value, and a kernel value, produce a Nix value.
# `reifyType` converts a kernel type value back to an HOAS type (used as
# fallback when the HOAS body cannot be recovered — dependent-type
# instantiation, polymorphic app-spine reduction). `reifyDesc` is the
# description-side counterpart consumed by `reifyType`'s VMu fallback.
#
# The Pi branch of `extractInner` wraps a Nix argument via
# `self.elaborateValue` before feeding it back into the kernel; the
# mutual recursion closes through `self`.
{ self, fx, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  V = fx.tc.value;
in {
  scope = {
    # reifyDesc : Val → HoasTree
    # Rebuild a kernel description value as an HOAS description term.
    # Anonymous — the kernel D alone carries no constructor/field names;
    # callers attach `_dtypeMeta` externally when named decomposition is
    # wanted.
    reifyDesc = dVal:
      let dt = dVal.tag; in
      if dt == "VDescRet" then H.descRet
      else if dt == "VDescRec" then H.descRec (self.reifyDesc dVal.D)
      else if dt == "VDescPi" then H.descPi (self.reifyType dVal.S) (self.reifyDesc dVal.D)
      else if dt == "VDescArg" then
        H.descArg (self.reifyType dVal.S)
          (x: self.reifyDesc (E.instantiate dVal.T (E.eval [] (H.elab x))))
      else throw "reifyDesc: unsupported VDesc tag '${dt}'";

    # reifyType : Val → HoasTree
    # Convert a kernel type value back to an HOAS type for extract dispatch.
    # Used as fallback when the HOAS body cannot be applied (dependent types)
    # and as the polymorphic-instantiation reducer for extractInner's "app"
    # branch. Loses sugar (VSigma → H.sigma, not H.record) — HOAS body is
    # preferred when available since it preserves record/variant/maybe
    # structure.
    #
    # The nat/list/sum reifications produce raw-tag HOAS attrsets rather
    # than the module-level `H.nat`/`H.listOf`/`H.sum` combinators. The
    # module-level combinators are app-spines (listOf/sum) or mu-forms
    # with `_dtypeMeta` (nat); feeding them back into `extractInner` would
    # re-enter the higher-level branches that reifyType is supposed to
    # terminate. The raw tags dispatch directly to the `"nat"`/`"list"`/
    # `"sum"` decoders in both `hoas.elaborate` and `extractInner`.
    reifyType = tyVal:
      let
        t = tyVal.tag;
        rawNat = { _htag = "nat"; };
        rawList = elem: { _htag = "list"; inherit elem; };
        rawSum = left: right: { _htag = "sum"; inherit left right; };
      in
      if t == "VNat" then rawNat
      else if t == "VBool" then H.bool
      else if t == "VString" then H.string
      else if t == "VUnit" then H.unit
      else if t == "VVoid" then H.void
      else if t == "VInt" then H.int_
      else if t == "VFloat" then H.float_
      else if t == "VAttrs" then H.attrs
      else if t == "VPath" then H.path
      else if t == "VFunction" then H.function_
      else if t == "VAny" then H.any
      else if t == "VList" then rawList (self.reifyType tyVal.elem)
      else if t == "VSum" then rawSum (self.reifyType tyVal.left) (self.reifyType tyVal.right)
      else if t == "VSigma" then
        H.sigma tyVal.name (self.reifyType tyVal.fst)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VPi" then
        H.forall tyVal.name (self.reifyType tyVal.domain)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VU" then H.u tyVal.level
      # VMu D — description-based fixpoints. Three sugar shapes are detected
      # first and reified to their named HOAS forms (preserves printed names
      # in error messages):
      #   natDesc:      subT = VDescRet;           subF = VDescRec VDescRet
      #   listDesc e:   subT = VDescRet;           subF = VDescArg e (_: …)
      #   sumDesc l r:  subT = VDescArg l (_: …);  subF = VDescArg r (_: …)
      # Anything else routes to the description-driven fallback `H.mu
      # (reifyDesc D)` — the resulting form is anonymous (no constructor /
      # field names) and is consumed by extractInner's "mu" branch which
      # optionally merges `_dtypeMeta` supplied by the caller for named
      # decomposition.
      else if t == "VMu" then
        let
          D = tyVal.D;
          fallback = H.mu (self.reifyDesc D);
        in
          if D.tag != "VDescArg" then fallback
          else
            let subT = E.instantiate D.T V.vTrue;
                subF = E.instantiate D.T V.vFalse; in
            if subT.tag == "VDescRet" && subF.tag == "VDescRec" then rawNat
            else if subT.tag == "VDescRet" && subF.tag == "VDescArg"
            then rawList (self.reifyType subF.S)
            else if subT.tag == "VDescArg" && subF.tag == "VDescArg"
            then rawSum (self.reifyType subT.S) (self.reifyType subF.S)
            else fallback
      else throw "reifyType: unsupported value tag '${t}'";

    # extractInner : HoasTree → Val → Val → NixValue
    # Three-argument extraction: HOAS type (for dispatch and sugar), kernel type
    # value (for dependent codomain/snd computation), and kernel value to extract.
    # Uses closure instantiation instead of sentinel tests for dependent types.
    extractInner = hoasTy: tyVal: val:
      let t = hoasTy._htag or (throw "extract: not an HOAS type"); in

      # Nat: base → 0, succ^n(base) → n. H.nat elaborates to μnatDesc, so every
      # value of type Nat arrives as a VDescCon chain:
      #   zero:   VDescCon natDesc (VPair VTrue VTt)
      #   succ p: VDescCon natDesc (VPair VFalse (VPair p VTt))
      # Trampolined via genericClosure for stack safety on large nats. The
      # operator does O(1) field projection on a concrete value; no deferred
      # continuation work accumulates, so the integer key suffices for dedup
      # and deepSeq-in-key would add O(N²) cost.
      if t == "nat" then
        let
          isDescSucc = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VFalse"
            && v.d.snd.tag == "VPair";
          isDescZero = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VTrue";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              if isDescSucc item.val
              then [{ key = item.key + 1; val = item.val.d.snd.fst; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
        in
          if isDescZero last.val
          then builtins.length chain - 1
          else throw "extract: Nat value is not a numeral (stuck at ${last.val.tag})"

      else if t == "bool" then
        if val.tag == "VTrue" then true
        else if val.tag == "VFalse" then false
        else throw "extract: Bool value is not true/false (got ${val.tag})"

      else if t == "unit" then
        if val.tag == "VTt" then null
        else throw "extract: Unit value is not tt (got ${val.tag})"

      else if t == "string" then
        if val.tag == "VStringLit" then val.value
        else throw "extract: String value is not a string literal (got ${val.tag})"

      else if t == "int" then
        if val.tag == "VIntLit" then val.value
        else throw "extract: Int value is not an int literal (got ${val.tag})"

      else if t == "float" then
        if val.tag == "VFloatLit" then val.value
        else throw "extract: Float value is not a float literal (got ${val.tag})"

      else if t == "attrs" then
        throw "extract: Attrs is opaque — kernel does not store attrset contents"

      else if t == "path" then
        throw "extract: Path is opaque — kernel does not store path value"

      else if t == "function" then
        throw "extract: Function is opaque — kernel does not store closure"

      else if t == "any" then
        throw "extract: Any is opaque — kernel does not store original value"

      else if t == "list" then
        # H.listOf elem elaborates to μ(listDesc elem), so every value of type
        # List arrives as a VDescCon chain:
        #   nil:       VDescCon D (VPair VTrue VTt)
        #   cons h t:  VDescCon D (VPair VFalse (VPair h (VPair t VTt)))
        # elemTyVal is recovered from the outer description by instantiating D
        # at vFalse: D = VDescArg bool T, T vFalse = descArg elem (_: descRec descRet),
        # whose .S is elem. Trampolined via genericClosure for stack safety.
        let
          elemTy = hoasTy.elem;
          isDescCons = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VFalse"
            && v.d.snd.tag == "VPair"
            && v.d.snd.snd.tag == "VPair";
          isDescNil = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VTrue";
          elemTyVal =
            if tyVal.tag == "VMu" && tyVal.D.tag == "VDescArg" then
              let subFalse = E.instantiate tyVal.D.T V.vFalse; in
              if subFalse.tag == "VDescArg" then subFalse.S
              else throw "extract: list tyVal has non-list description (sub-false=${subFalse.tag})"
            else throw "extract: list tyVal must be VMu(listDesc), got ${tyVal.tag}";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              if isDescCons item.val
              then [{ key = item.key + 1; val = item.val.d.snd.snd.fst; }]
              else [];
          };
          n = builtins.length chain;
          last = builtins.elemAt chain (n - 1);
        in
          if !(isDescNil last.val)
          then throw "extract: List is not a proper cons/nil chain (stuck at ${last.val.tag})"
          else builtins.genList (i:
            let item = (builtins.elemAt chain i).val; in
            self.extractInner elemTy elemTyVal item.d.snd.fst
          ) (n - 1)

      else if t == "sum" then
        # H.sum l r elaborates to μ(sumDesc l r), so every value of type Sum
        # arrives as a single-layer VDescCon:
        #   inl a: VDescCon D (VPair VTrue  (VPair a VTt))
        #   inr b: VDescCon D (VPair VFalse (VPair b VTt))
        # Branch element type is recovered from D by instantiating at vTrue /
        # vFalse: each yields VDescArg l/r (_: descRet), whose .S is the arm.
        let
          isDescInl = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VTrue"
            && v.d.snd.tag == "VPair";
          isDescInr = v:
            v.tag == "VDescCon"
            && v.d.tag == "VPair"
            && v.d.fst.tag == "VFalse"
            && v.d.snd.tag == "VPair";
          armTy = tag:
            if tyVal.tag == "VMu" && tyVal.D.tag == "VDescArg" then
              let sub = E.instantiate tyVal.D.T
                          (if tag == "VTrue" then V.vTrue else V.vFalse); in
              if sub.tag == "VDescArg" then sub.S
              else throw "extract: sum tyVal has non-sum description (sub-${tag}=${sub.tag})"
            else throw "extract: sum tyVal must be VMu(sumDesc), got ${tyVal.tag}";
        in
        if isDescInl val then
          { _tag = "Left"; value = self.extractInner hoasTy.left (armTy "VTrue") val.d.snd.fst; }
        else if isDescInr val then
          { _tag = "Right"; value = self.extractInner hoasTy.right (armTy "VFalse") val.d.snd.fst; }
        else throw "extract: Sum value is neither inl nor inr (got ${val.tag})"

      else if t == "sigma" then
        let
          fstNix = self.extractInner hoasTy.fst tyVal.fst val.fst;
          sndTyVal = E.instantiate tyVal.closure val.fst;
          r = builtins.tryEval (hoasTy.body { _htag = "unit"; });
          sndHoas = if r.success then r.value else self.reifyType sndTyVal;
        in { fst = fstNix; snd = self.extractInner sndHoas sndTyVal val.snd; }

      # -- Compound types (record, maybe, variant) --

      else if t == "record" then
        let
          fields = hoasTy.fields;
          n = builtins.length fields;
        in
          if n == 0 then {}
          else if n == 1 then
            { ${(builtins.head fields).name} = self.extractInner (builtins.head fields).type tyVal val; }
          else
            let
              extractFields = remaining: tyV: v:
                if builtins.length remaining == 1 then
                  { ${(builtins.head remaining).name} = self.extractInner (builtins.head remaining).type tyV v; }
                else
                  let
                    f = builtins.head remaining;
                    rest = builtins.tail remaining;
                    sndTyVal = E.instantiate tyV.closure v.fst;
                  in
                  { ${f.name} = self.extractInner f.type tyV.fst v.fst; }
                  // extractFields rest sndTyVal v.snd;
            in extractFields fields tyVal val

      else if t == "maybe" then
        # Maybe = Sum(inner, Unit). VInl = value present, VInr = null
        if val.tag == "VInl" then self.extractInner hoasTy.inner tyVal.left val.val
        else if val.tag == "VInr" then null
        else throw "extract: Maybe value is neither inl nor inr (got ${val.tag})"

      else if t == "variant" then
        let
          branches = hoasTy.branches;
          extractBranch = bs: tyV: v:
            let n = builtins.length bs; in
            if n == 1 then
              { _tag = (builtins.head bs).tag; value = self.extractInner (builtins.head bs).type tyV v; }
            else
              let b1 = builtins.head bs; rest = builtins.tail bs; in
              if v.tag == "VInl" then
                { _tag = b1.tag; value = self.extractInner b1.type tyV.left v.val; }
              else if v.tag == "VInr" then
                extractBranch rest tyV.right v.val
              else throw "extract: Variant value is neither inl nor inr (got ${v.tag})";
        in extractBranch branches tyVal val

      else if t == "pi" then
        # Opaque lambda: return the original Nix function directly.
        # No kernel extraction needed — the function was carried opaquely.
        if val.tag == "VOpaqueLam" then val.nixFn
        # Verified lambda: extract via kernel pipeline.
        # Returns a Nix function that:
        #   1. Elaborates its argument to HOAS → kernel value
        #   2. Applies the VLam closure
        #   3. Extracts the result back to a Nix value
        # Codomain type is computed per-invocation from the type's closure,
        # supporting both dependent and non-dependent Pi.
        else let domainTy = hoasTy.domain; in
          nixArg:
            let
              hoasArg = self.elaborateValue domainTy nixArg;
              kernelArg = E.eval [] (H.elab hoasArg);
              resultVal = E.instantiate val.closure kernelArg;
              codomainTyVal = E.instantiate tyVal.closure kernelArg;
              r = builtins.tryEval (hoasTy.body hoasArg);
              codomainHoas = if r.success then r.value else self.reifyType codomainTyVal;
            in self.extractInner codomainHoas codomainTyVal resultVal

      # Description-based fixpoints. Detect prelude-equivalent shapes by
      # structure and delegate to the nat/list/sum branches to preserve
      # the same Nix output for shape-equivalent values. Bool-shape and
      # Unit-shape values (no dedicated "bool"/"unit" branch handles their
      # VDescCon wrapping) decode inline to Nix bool / null. Other shapes
      # decompose generically into a constructor record using `_dtypeMeta`
      # for naming; without metadata, names are positional ("con0" /
      # "_field0").
      else if t == "mu" then
        let
          descTyVal = tyVal.D;
          meta = hoasTy._dtypeMeta or null;

          # Description-shape predicates. All require D to be `VDescArg bool
          # (b: …)` (the macro's n>=2 spine) except isUnitDTShape (n=1).
          boolHeaded = d:
            d.tag == "VDescArg" && d.S.tag == "VBool";
          # NatDT: subT=descRet, subF=descRec descRet.
          isNatDesc = d:
            boolHeaded d &&
            (let subT = E.instantiate d.T V.vTrue;
                 subF = E.instantiate d.T V.vFalse; in
             subT.tag == "VDescRet" && subF.tag == "VDescRec"
             && subF.D.tag == "VDescRet");
          # ListDT(elem): subT=descRet, subF=descArg elem (_: descRec descRet).
          # The inner body is checked by instantiating subF.T at vFalse — the
          # closure's argument is unused for ListDT (`_: descRec descRet`)
          # so vFalse is a safe placeholder.
          isListDesc = d:
            boolHeaded d &&
            (let subT = E.instantiate d.T V.vTrue;
                 subF = E.instantiate d.T V.vFalse; in
             subT.tag == "VDescRet" && subF.tag == "VDescArg"
             && (let body = E.instantiate subF.T V.vFalse; in
                 body.tag == "VDescRec" && body.D.tag == "VDescRet"));
          # SumDT(l,r): subT=descArg l (_: descRet), subF=descArg r (_: descRet).
          isSumDesc = d:
            boolHeaded d &&
            (let subT = E.instantiate d.T V.vTrue;
                 subF = E.instantiate d.T V.vFalse; in
             subT.tag == "VDescArg" && subF.tag == "VDescArg"
             && (let bT = E.instantiate subT.T V.vFalse;
                     bF = E.instantiate subF.T V.vFalse; in
                 bT.tag == "VDescRet" && bF.tag == "VDescRet"));
          # BoolDT shape: subT=descRet, subF=descRet (n=2, both ctors fieldless).
          isBoolDTShape = d:
            boolHeaded d &&
            (let subT = E.instantiate d.T V.vTrue;
                 subF = E.instantiate d.T V.vFalse; in
             subT.tag == "VDescRet" && subF.tag == "VDescRet");
          # UnitDT shape: bare descRet (n=1).
          isUnitDTShape = d:
            d.tag == "VDescRet";

          # Generic decomposition for non-prelude shapes. Walks the Bool-tag
          # spine to determine the constructor index, then walks the per-arm
          # data spine to extract fields. `pickArm` recurses through nested
          # `VDescArg bool (b: boolElim _ <arm-i> <rest-spine> b)` layers
          # produced by `spineDesc`; advances ctorIdx on every VFalse step.
          # `extractFields` recurses through the per-arm data spine
          # (VDescArg → field, VDescRec → recursive value, VDescPi → opaque
          # function, VDescRet → terminus).
          pickArm = idx: dTy: pl:
            if dTy.tag == "VDescArg" && dTy.S.tag == "VBool" then
              let tagVal = pl.fst;
                  subPayload = pl.snd; in
              if tagVal.tag == "VTrue" then
                pickArm idx (E.instantiate dTy.T V.vTrue) subPayload
              else if tagVal.tag == "VFalse" then
                pickArm (idx + 1) (E.instantiate dTy.T V.vFalse) subPayload
              else throw "extract: mu tag is neither VTrue/VFalse (got ${tagVal.tag})"
            else { ctorIdx = idx; armDesc = dTy; armPayload = pl; };
          extractFields = dTy: pl:
            if dTy.tag == "VDescRet" then []
            else if dTy.tag == "VDescArg" then
              let fieldVal = pl.fst;
                  rest = pl.snd;
                  fieldHoas = self.reifyType dTy.S;
                  fieldNix = self.extractInner fieldHoas dTy.S fieldVal;
                  subDesc = E.instantiate dTy.T fieldVal;
              in [ fieldNix ] ++ extractFields subDesc rest
            else if dTy.tag == "VDescRec" then
              let recVal = pl.fst;
                  rest = pl.snd;
                  recNix = self.extractInner hoasTy tyVal recVal;
              in [ recNix ] ++ extractFields dTy.D rest
            else if dTy.tag == "VDescPi" then
              # Opaque lambda field: return the kernel VLam wrapped as a
              # Nix function via the existing pi-extract discipline. Domain
              # is reified; codomain is the outer mu's hoasTy (rec under Pi).
              let lamVal = pl.fst;
                  rest = pl.snd;
                  domainHoas = self.reifyType dTy.S;
                  piHoas = H.forall "_" domainHoas (_: hoasTy);
                  piTyVal = V.vPi "_" dTy.S (V.mkClosure [] (H.elab hoasTy));
                  lamNix = self.extractInner piHoas piTyVal lamVal;
              in [ lamNix ] ++ extractFields dTy.D rest
            else throw "extract: mu generic decomposition: unsupported VDesc tag '${dTy.tag}'";

        in
        if val.tag != "VDescCon"
        then throw "extract: mu value is not a VDescCon (got ${val.tag})"
        else if isUnitDTShape descTyVal then null
        else if isBoolDTShape descTyVal then
          if val.d.fst.tag == "VTrue" then true
          else if val.d.fst.tag == "VFalse" then false
          else throw "extract: BoolDT-shape value tag is neither VTrue/VFalse (got ${val.d.fst.tag})"
        else if isNatDesc descTyVal
        then self.extractInner { _htag = "nat"; } tyVal val
        else if isListDesc descTyVal then
          let elemTyVal = (E.instantiate descTyVal.T V.vFalse).S;
          in self.extractInner { _htag = "list"; elem = self.reifyType elemTyVal; } tyVal val
        else if isSumDesc descTyVal then
          let leftTyVal = (E.instantiate descTyVal.T V.vTrue).S;
              rightTyVal = (E.instantiate descTyVal.T V.vFalse).S;
          in self.extractInner {
            _htag = "sum";
            left = self.reifyType leftTyVal;
            right = self.reifyType rightTyVal;
          } tyVal val
        else
          let
            arm = pickArm 0 descTyVal val.d;
            fieldVals = extractFields arm.armDesc arm.armPayload;
            conName =
              if meta != null
              then (builtins.elemAt meta.cons arm.ctorIdx).name
              else "con${toString arm.ctorIdx}";
            fieldNames =
              if meta != null
              then map (f: f.name) (builtins.elemAt meta.cons arm.ctorIdx).fields
              else builtins.genList (i: "_field${toString i}") (builtins.length fieldVals);
          in
            { _con = conName; }
            // builtins.listToAttrs (builtins.genList (i: {
                 name = builtins.elemAt fieldNames i;
                 value = builtins.elemAt fieldVals i;
               }) (builtins.length fieldVals))

      # Polymorphic-instantiation surface: hoasTy is `app^k head A1 ... Ak`
      # where `head` is the macro's `polyField "T"` carrying `_dtypeMeta`.
      # tyVal is the kernel value computed by extract (`E.eval [] (H.elab
      # hoasTy)`), already β-reduced past the application — typically a VMu.
      # Reify the type to obtain a tag-dispatchable HOAS form, propagate
      # `_dtypeMeta` from the head if present (so the mu-branch generic
      # decomposition can name constructors), and recurse.
      else if t == "app" then
        let
          peelHead = node:
            if (builtins.isAttrs node) && (node._htag or null) == "app"
            then peelHead node.fn
            else node;
          head = peelHead hoasTy;
          headMeta = head._dtypeMeta or null;
          base = self.reifyType tyVal;
          hoasTy' =
            if headMeta != null && (base._htag or null) == "mu"
            then base // { _dtypeMeta = headMeta; }
            else base;
        in self.extractInner hoasTy' tyVal val

      else throw "extract: unsupported type '${t}'";
  };

  tests = {};
}
