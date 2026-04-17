# Type-checking kernel: Elaboration bridge
#
# Bridges fx.types to kernel term representation (de Bruijn Tm)
# via the HOAS surface combinator layer.
#
# Eight operations:
#   elaborateType    : FxType → HoasTree              (type level)
#   elaborateValue   : HoasTree → NixVal → HoasTree   (value level: Nix → HOAS)
#   validateValue    : String → HoasTree → NixVal → [Error]  (structural validation)
#   extract          : HoasTree → Val → NixValue       (value level: kernel → Nix)
#   extractInner     : HoasTree → Val → Val → NixValue (3-arg: HOAS + type val + val)
#   reifyType        : Val → HoasTree                  (kernel type val → HOAS fallback)
#   decide           : HoasTree → NixVal → Bool        (decision procedure)
#   decideType       : FxType → NixVal → Bool          (elaborate type then decide)
#   verifyAndExtract : HoasTree → HoasTree → NixValue  (full pipeline)
#
# elaborateType dispatches on:
#   1. _kernel field (types built via mkType with kernelType)
#   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
#   3. Name convention (Bool, Nat, Unit, Null, String, Int, Float, ...)
#
# elaborateValue uses HOAS substitution for dependent Sigma (body(â)).
# extract uses kernel type value threading (no sentinel tests).
#
# Spec reference: kernel-mvp-research.md §3
{ fx, api, ... }:

let
  inherit (api) mk;
  H = fx.tc.hoas;
  E = fx.tc.eval;
  V = fx.tc.value;

  # -- Detection predicates for fx.types structural dispatch --

  # Pi types carry domain, codomain, checkAt from dependent.nix
  isPi = type:
    builtins.isAttrs type
    && type ? domain && type ? codomain && type ? checkAt;

  # Sigma types carry fstType, sndFamily, proj1 from dependent.nix
  isSigma = type:
    builtins.isAttrs type
    && type ? fstType && type ? sndFamily && type ? proj1;

  # Non-dependence test: call the family with two sentinels.
  # If result type names match, the family is constant.
  # LIMITATION: builtins.tryEval only catches `throw` and `assert false`.
  # A type family that triggers boolean coercion errors, cross-type comparison
  # errors, or missing attribute access on sentinels will crash Nix rather than
  # returning false from isConstantFamily. This is an inherent limitation of
  # Nix's error model — there is no general-purpose exception catching.
  _s1 = { _tag = "Type"; name = "__elab_sentinel_1__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  _s2 = { _tag = "Type"; name = "__elab_sentinel_2__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  isConstantFamily = fn:
    let
      r1 = builtins.tryEval (fn _s1);
      r2 = builtins.tryEval (fn _s2);
    in r1.success && r2.success && r1.value.name == r2.value.name;

  # -- Type elaboration --
  #
  # Dispatches on:
  #   1. _kernel annotation (annotated types from this module)
  #   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
  #   3. Name convention (Bool, Nat, Unit, Null)
  elaborateType = type:
    if !(builtins.isAttrs type) then
      throw "elaborateType: expected a type attrset"
    else if type ? prove then type._kernel
    else if isPi type then
      if isConstantFamily type.codomain
      then H.forall "x" (elaborateType type.domain) (_: elaborateType (type.codomain _s1))
      else throw "elaborateType: dependent Pi requires _kernel annotation"
    else if isSigma type then
      if isConstantFamily type.sndFamily
      then H.sigma "x" (elaborateType type.fstType) (_: elaborateType (type.sndFamily _s1))
      else throw "elaborateType: dependent Sigma requires _kernel annotation"
    else if type.name == "Bool" then H.bool
    else if type.name == "Nat" then H.nat
    else if type.name == "Unit" || type.name == "Null" then H.unit
    else if type.name == "String" then H.string
    else if type.name == "Int" then H.int_
    else if type.name == "Float" then H.float_
    else if type.name == "Attrs" then H.attrs
    else if type.name == "Path" then H.path
    else if type.name == "Function" then H.function_
    else if type.name == "Any" then H.any
    else throw "elaborateType: cannot elaborate '${type.name}' (add _kernel annotation)";

  # -- Value elaboration --
  #
  # Dispatches on HOAS type tag (_htag) to produce HOAS value tree.
  # Guards ensure clean throws (catchable by tryEval) for invalid values.
  elaborateValue = hoasTy: value:
    let t = hoasTy._htag or (throw "elaborateValue: not an HOAS type node"); in

    if t == "bool" then
      if !(builtins.isBool value)
      then throw "elaborateValue: Bool requires boolean, got ${builtins.typeOf value}"
      else if value then H.true_ else H.false_

    else if t == "nat" then
      if !(builtins.isInt value) || value < 0
      then throw "elaborateValue: Nat requires non-negative integer"
      else H.natLit value

    else if t == "unit" then
      if value != null
      then throw "elaborateValue: Unit requires null"
      else H.tt

    else if t == "string" then
      if !(builtins.isString value)
      then throw "elaborateValue: String requires string, got ${builtins.typeOf value}"
      else H.stringLit value

    else if t == "int" then
      if !(builtins.isInt value)
      then throw "elaborateValue: Int requires integer, got ${builtins.typeOf value}"
      else H.intLit value

    else if t == "float" then
      if !(builtins.isFloat value)
      then throw "elaborateValue: Float requires float, got ${builtins.typeOf value}"
      else H.floatLit value

    else if t == "attrs" then
      if !(builtins.isAttrs value)
      then throw "elaborateValue: Attrs requires attrset, got ${builtins.typeOf value}"
      else H.attrsLit

    else if t == "path" then
      if !(builtins.isPath value)
      then throw "elaborateValue: Path requires path, got ${builtins.typeOf value}"
      else H.pathLit

    else if t == "function" then
      if !(builtins.isFunction value)
      then throw "elaborateValue: Function requires function, got ${builtins.typeOf value}"
      else H.fnLit

    else if t == "any" then H.anyLit

    else if t == "U" then
      # Universe types: a type-as-value in U(n) elaborates to its kernel
      # representation. The kernel's checkTypeLevel verifies the level.
      if builtins.isAttrs value && value ? _kernel then value._kernel
      else throw "elaborateValue: U requires a Type with _kernel"

    else if t == "list" then
      if !(builtins.isList value)
      then throw "elaborateValue: List requires a list"
      else
        let
          elemTy = hoasTy.elem;
          len = builtins.length value;
        in builtins.foldl' (acc: i:
          let v = builtins.elemAt value (len - 1 - i); in
          H.cons elemTy (elaborateValue elemTy v) acc
        ) (H.nil elemTy) (builtins.genList (x: x) len)

    else if t == "sum" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then throw "elaborateValue: Sum requires { _tag = \"Left\"|\"Right\"; value = ...; }"
      else if value._tag == "Left"
      then H.inl hoasTy.left hoasTy.right (elaborateValue hoasTy.left value.value)
      else if value._tag == "Right"
      then H.inr hoasTy.left hoasTy.right (elaborateValue hoasTy.right value.value)
      else throw "elaborateValue: Sum _tag must be \"Left\" or \"Right\""

    else if t == "sigma" then
      if !(builtins.isAttrs value && value ? fst && value ? snd)
      then throw "elaborateValue: Sigma requires { fst; snd; }"
      else
        let
          # HOAS substitution: elaborate fst, pass to body for dependent snd type.
          # For non-dependent bodies, body ignores its argument — identical result.
          # For dependent bodies, body(â) computes the correct snd type via
          # meta-level function application (HOAS-level substitution).
          fstHoas = elaborateValue hoasTy.fst value.fst;
          sndTy = hoasTy.body fstHoas;
        in H.pair
          fstHoas
          (elaborateValue sndTy value.snd)

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      let
        fields = hoasTy.fields;
        n = builtins.length fields;
        # Safe field access: converts uncatchable missing-attribute error
        # to catchable throw so that decide remains total for records.
        fieldOf = v: name:
          if v ? ${name} then v.${name}
          else throw "elaborateValue: Record missing required field '${name}'";
      in
        if !(builtins.isAttrs value)
        then throw "elaborateValue: Record requires attrset, got ${builtins.typeOf value}"
        else if n == 0 then H.tt
        else if n == 1 then
          let f = builtins.head fields; in
          elaborateValue f.type (fieldOf value f.name)
        else
          # Build nested pairs right-to-left
          let
            buildPairs = remaining: v:
              if builtins.length remaining == 1 then
                elaborateValue (builtins.head remaining).type (fieldOf v (builtins.head remaining).name)
              else
                let
                  f = builtins.head remaining;
                  rest = builtins.tail remaining;
                  sigTy = H.sigma f.name f.type (_: { _htag = "record"; fields = rest; });
                in H.pair
                  (elaborateValue f.type (fieldOf v f.name))
                  (buildPairs rest v);
          in buildPairs fields value

    else if t == "maybe" then
      # Maybe = Sum(inner, Unit). null → Right(tt), value → Left(value)
      if value == null
      then H.inr hoasTy.inner H.unit H.tt
      else H.inl hoasTy.inner H.unit (elaborateValue hoasTy.inner value)

    else if t == "variant" then
      let branches = hoasTy.branches; in
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then throw "elaborateValue: Variant requires { _tag; value; }"
      else
        let
          # Find the matching branch and build nested inl/inr injection
          inject = bs: v:
            let n = builtins.length bs; in
            if n == 1 then
              elaborateValue (builtins.head bs).type v.value
            else
              let
                b1 = builtins.head bs;
                rest = builtins.tail bs;
                restTy = { _htag = "variant"; branches = rest; };
              in
                if v._tag == b1.tag
                then H.inl b1.type restTy (elaborateValue b1.type v.value)
                else H.inr b1.type restTy (inject rest v);
        in inject branches value

    else if t == "pi" then
      # Verified-first dispatch: if value carries _hoasImpl (from verified
      # combinators), use it for full kernel body verification. Otherwise,
      # wrap the raw Nix function in an opaque lambda (trust boundary).
      if builtins.isAttrs value && value ? _hoasImpl then value._hoasImpl
      else if builtins.isFunction value then H.opaqueLam value hoasTy
      else throw "elaborateValue: Pi type expects function, got ${builtins.typeOf value}"

    # μ-form types — covers `H.nat` (monomorphic, `_htag="mu"` with
    # `_dtypeMeta`) and any raw `mu D` construction whose description
    # reifies into one of the three prelude shapes. Detects shape by
    # instantiating the description's bool-tag body and delegates to the
    # corresponding "nat"/"list"/"sum" branches (which carry the
    # Nix-level encoders). Element types for list/sum shapes are
    # recovered via `reifyType` — the lossy fallback when no HOAS
    # surface is available. The primary path for `H.listOf`/`H.sum` is
    # the app-branch below, which preserves parameter HOAS directly.
    else if t == "mu" then
      let
        tyVal = E.eval [] (H.elab hoasTy);
        D = tyVal.D;
      in
      if D.tag != "VDescArg" || D.S.tag != "VBool"
      then throw "elaborateValue: unsupported μ-shape (D.tag=${D.tag})"
      else
        let
          subT = E.instantiate D.T V.vTrue;
          subF = E.instantiate D.T V.vFalse;
        in
        if subT.tag == "VDescRet" && subF.tag == "VDescRec"
        then elaborateValue { _htag = "nat"; } value
        else if subT.tag == "VDescRet" && subF.tag == "VDescArg"
        then elaborateValue
               { _htag = "list"; elem = reifyType subF.S; }
               value
        else if subT.tag == "VDescArg" && subF.tag == "VDescArg"
        then elaborateValue
               { _htag = "sum";
                 left = reifyType subT.S;
                 right = reifyType subF.S; }
               value
        else throw "elaborateValue: unsupported μ-shape (subT=${subT.tag}, subF=${subF.tag})"

    # App-spine types — `app^k head A1 … Ak` where `head` is a polyField
    # carrying `_dtypeMeta` (e.g. `ListDT.T`/`SumDT.T` from `H.listOf`/
    # `H.sum`, or any user-defined `datatypeP`-produced `T`). The app
    # spine keeps each parameter HOAS as a structural slot, so surface
    # sugar (record, variant, maybe) survives the indirection through
    # the macro. `_dtypeMeta.cons` classifies the datatype's shape and
    # dispatches the value walker; the literal app args are reused as
    # the element HOAS, never round-tripped through a kernel value.
    else if t == "app" then
      let
        peelSpine = node: args:
          if (builtins.isAttrs node) && (node._htag or null) == "app"
          then peelSpine node.fn ([ node.arg ] ++ args)
          else { head = node; inherit args; };
        spine = peelSpine hoasTy [];
        head = spine.head;
        args = spine.args;
        meta = head._dtypeMeta or null;
        fieldKinds = c: map (f: f.kind) c.fields;
        isListShape = m:
          builtins.length m.cons == 2
          && fieldKinds (builtins.elemAt m.cons 0) == []
          && fieldKinds (builtins.elemAt m.cons 1) == [ "data" "rec" ];
        isSumShape = m:
          builtins.length m.cons == 2
          && fieldKinds (builtins.elemAt m.cons 0) == [ "data" ]
          && fieldKinds (builtins.elemAt m.cons 1) == [ "data" ];
      in
      if meta == null
      then throw "elaborateValue: app head carries no _dtypeMeta (non-datatype app has no value-walker)"
      else if isListShape meta && builtins.length args == 1
      then elaborateValue { _htag = "list"; elem = builtins.elemAt args 0; } value
      else if isSumShape meta && builtins.length args == 2
      then elaborateValue {
        _htag = "sum";
        left = builtins.elemAt args 0;
        right = builtins.elemAt args 1;
      } value
      else throw "elaborateValue: app-form datatype '${meta.name}' has no dedicated walker (shape: ${builtins.toJSON (map fieldKinds meta.cons)})"

    else throw "elaborateValue: unsupported type tag '${t}'";

  # -- Structural validation --
  #
  # validateValue : String → HoasTree → NixVal → [{ path; msg; }]
  #
  # Mirrors elaborateValue's structural recursion over HOAS type tags but
  # returns a list of errors instead of producing HOAS terms or throwing.
  # Empty list means the value would elaborate successfully.
  #
  # Design:
  #   elaborateValue is monadic (Either) — fails fast on the first error.
  #   validateValue is applicative (Validation) — accumulates all errors.
  #   These are different morphisms: one produces values, the other diagnostics.
  #   The path accumulator is the Reader effect (inherited attribute in the fold).
  #   The error list is the Writer effect (free monoid).
  #
  # Soundness: checks the same predicates as elaborateValue. If validateValue
  # returns [] then elaborateValue will not throw (and vice versa). Both have
  # catch-all branches for unknown tags, so they cannot silently diverge.
  validateValue = path: hoasTy: value:
    let t = hoasTy._htag or "invalid"; in

    # -- Scalar types --

    if t == "bool" then
      if !(builtins.isBool value)
      then [{ inherit path; msg = "expected bool, got ${builtins.typeOf value}"; }]
      else []

    else if t == "nat" then
      if !(builtins.isInt value) || value < 0
      then [{ inherit path; msg = "expected non-negative integer, got ${builtins.typeOf value}"; }]
      else []

    else if t == "unit" then
      if value != null
      then [{ inherit path; msg = "expected null (unit), got ${builtins.typeOf value}"; }]
      else []

    else if t == "string" then
      if !(builtins.isString value)
      then [{ inherit path; msg = "expected string, got ${builtins.typeOf value}"; }]
      else []

    else if t == "int" then
      if !(builtins.isInt value)
      then [{ inherit path; msg = "expected integer, got ${builtins.typeOf value}"; }]
      else []

    else if t == "float" then
      if !(builtins.isFloat value)
      then [{ inherit path; msg = "expected float, got ${builtins.typeOf value}"; }]
      else []

    else if t == "attrs" then
      if !(builtins.isAttrs value)
      then [{ inherit path; msg = "expected attrset, got ${builtins.typeOf value}"; }]
      else []

    else if t == "path" then
      if !(builtins.isPath value)
      then [{ inherit path; msg = "expected path, got ${builtins.typeOf value}"; }]
      else []

    else if t == "function" then
      if !(builtins.isFunction value)
      then [{ inherit path; msg = "expected function, got ${builtins.typeOf value}"; }]
      else []

    else if t == "any" then []

    else if t == "U" then
      if builtins.isAttrs value && value ? _kernel then []
      else [{ inherit path; msg = "expected Type with _kernel"; }]

    # -- List: validate every element with indexed path --

    else if t == "list" then
      if !(builtins.isList value)
      then [{ inherit path; msg = "expected list, got ${builtins.typeOf value}"; }]
      else
        let
          elemTy = hoasTy.elem;
          len = builtins.length value;
        in builtins.concatMap (i:
          validateValue "${path}[${toString i}]" elemTy (builtins.elemAt value i)
        ) (builtins.genList (x: x) len)

    # -- Sum: validate tag structure then recurse into branch --

    else if t == "sum" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then [{ inherit path; msg = "expected { _tag = \"Left\"|\"Right\"; value = ...; }"; }]
      else if value._tag == "Left" then validateValue "${path}.Left" hoasTy.left value.value
      else if value._tag == "Right" then validateValue "${path}.Right" hoasTy.right value.value
      else [{ inherit path; msg = "_tag must be \"Left\" or \"Right\", got \"${value._tag}\""; }]

    # -- Sigma: HOAS substitution for dependent snd type --

    else if t == "sigma" then
      if !(builtins.isAttrs value && value ? fst && value ? snd)
      then [{ inherit path; msg = "expected { fst; snd; }"; }]
      else
        let
          fstErrors = validateValue "${path}.fst" hoasTy.fst value.fst;
          # Attempt fst elaboration for HOAS substitution into body.
          # If fst elaboration fails, report fst errors only — computing
          # snd type requires a valid fst HOAS term.
          fstElab = builtins.tryEval (elaborateValue hoasTy.fst value.fst);
        in
        if !fstElab.success then fstErrors
        else
          let sndTy = hoasTy.body fstElab.value;
          in fstErrors
             ++ (validateValue "${path}.snd" sndTy value.snd)

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      if !(builtins.isAttrs value)
      then [{ inherit path; msg = "expected record (attrset), got ${builtins.typeOf value}"; }]
      else
        builtins.concatMap (f:
          if !(builtins.hasAttr f.name value)
          then [{ path = "${path}.${f.name}"; msg = "missing required field"; }]
          else validateValue "${path}.${f.name}" f.type value.${f.name}
        ) (hoasTy.fields or [])

    else if t == "maybe" then
      if value == null then []
      else validateValue path hoasTy.inner value

    else if t == "variant" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then [{ inherit path; msg = "expected { _tag; value; }"; }]
      else
        let
          branches = hoasTy.branches;
          matching = builtins.filter (b: b.tag == value._tag) branches;
        in
        if matching == []
        then [{ inherit path; msg = "unknown variant tag \"${value._tag}\"; expected one of: ${builtins.concatStringsSep ", " (map (b: "\"${b.tag}\"") branches)}"; }]
        else validateValue "${path}.${value._tag}" (builtins.head matching).type value.value

    else if t == "pi" then
      if (builtins.isAttrs value && value ? _hoasImpl) || builtins.isFunction value then []
      else [{ inherit path; msg = "expected function, got ${builtins.typeOf value}"; }]

    # μ-form types — mirror the elaborateValue "mu" branch: detect prelude
    # shape via kernel-description instantiation and delegate to the
    # corresponding nat/list/sum branch.
    else if t == "mu" then
      let
        tyVal = E.eval [] (H.elab hoasTy);
        D = tyVal.D;
      in
      if D.tag != "VDescArg" || D.S.tag != "VBool"
      then [{ inherit path; msg = "unsupported μ-shape (D.tag=${D.tag})"; }]
      else
        let
          subT = E.instantiate D.T V.vTrue;
          subF = E.instantiate D.T V.vFalse;
        in
        if subT.tag == "VDescRet" && subF.tag == "VDescRec"
        then validateValue path { _htag = "nat"; } value
        else if subT.tag == "VDescRet" && subF.tag == "VDescArg"
        then validateValue path
               { _htag = "list"; elem = reifyType subF.S; }
               value
        else if subT.tag == "VDescArg" && subF.tag == "VDescArg"
        then validateValue path
               { _htag = "sum";
                 left = reifyType subT.S;
                 right = reifyType subF.S; }
               value
        else [{ inherit path; msg = "unsupported μ-shape (subT=${subT.tag}, subF=${subF.tag})"; }]

    # App-spine types — mirror of elaborateValue's "app" branch. Peel the
    # spine to the polyField head, read `_dtypeMeta.cons` for shape
    # classification, delegate to the list/sum branch with the literal
    # parameter HOAS preserved.
    else if t == "app" then
      let
        peelSpine = node: args:
          if (builtins.isAttrs node) && (node._htag or null) == "app"
          then peelSpine node.fn ([ node.arg ] ++ args)
          else { head = node; inherit args; };
        spine = peelSpine hoasTy [];
        head = spine.head;
        args = spine.args;
        meta = head._dtypeMeta or null;
        fieldKinds = c: map (f: f.kind) c.fields;
        isListShape = m:
          builtins.length m.cons == 2
          && fieldKinds (builtins.elemAt m.cons 0) == []
          && fieldKinds (builtins.elemAt m.cons 1) == [ "data" "rec" ];
        isSumShape = m:
          builtins.length m.cons == 2
          && fieldKinds (builtins.elemAt m.cons 0) == [ "data" ]
          && fieldKinds (builtins.elemAt m.cons 1) == [ "data" ];
      in
      if meta == null
      then [{ inherit path; msg = "app head carries no _dtypeMeta (non-datatype app has no value-walker)"; }]
      else if isListShape meta && builtins.length args == 1
      then validateValue path
             { _htag = "list"; elem = builtins.elemAt args 0; }
             value
      else if isSumShape meta && builtins.length args == 2
      then validateValue path {
        _htag = "sum";
        left = builtins.elemAt args 0;
        right = builtins.elemAt args 1;
      } value
      else [{ inherit path; msg = "app-form datatype '${meta.name}' has no dedicated walker"; }]

    else [{ inherit path; msg = "unsupported type tag '${t}'"; }];

  # -- Reification: kernel type value → HOAS type --
  #
  # reifyType : Val → HoasTree
  # Converts a kernel type value back to an HOAS type for extract dispatch.
  # Used as fallback when the HOAS body cannot be applied (dependent types)
  # and as the polymorphic-instantiation reducer for extractInner's "app"
  # branch. Loses sugar (VSigma → H.sigma, not H.record) — HOAS body is
  # preferred when available since it preserves record/variant/maybe
  # structure.
  #
  # `reifyDesc` is the description-side counterpart, used by the "mu"
  # fallback to rebuild a kernel description value as an HOAS description
  # term. Anonymous (no constructor / field names recoverable from the
  # kernel D alone — callers attach `_dtypeMeta` externally if needed).
  reifyDesc = dVal:
    let dt = dVal.tag; in
    if dt == "VDescRet" then H.descRet
    else if dt == "VDescRec" then H.descRec (reifyDesc dVal.D)
    else if dt == "VDescPi" then H.descPi (reifyType dVal.S) (reifyDesc dVal.D)
    else if dt == "VDescArg" then
      H.descArg (reifyType dVal.S)
        (x: reifyDesc (E.instantiate dVal.T (E.eval [] (H.elab x))))
    else throw "reifyDesc: unsupported VDesc tag '${dt}'";

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
    else if t == "VList" then rawList (reifyType tyVal.elem)
    else if t == "VSum" then rawSum (reifyType tyVal.left) (reifyType tyVal.right)
    else if t == "VSigma" then
      H.sigma tyVal.name (reifyType tyVal.fst)
        (x: reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
    else if t == "VPi" then
      H.forall tyVal.name (reifyType tyVal.domain)
        (x: reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
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
        fallback = H.mu (reifyDesc D);
      in
        if D.tag != "VDescArg" then fallback
        else
          let subT = E.instantiate D.T V.vTrue;
              subF = E.instantiate D.T V.vFalse; in
          if subT.tag == "VDescRet" && subF.tag == "VDescRec" then rawNat
          else if subT.tag == "VDescRet" && subF.tag == "VDescArg"
          then rawList (reifyType subF.S)
          else if subT.tag == "VDescArg" && subF.tag == "VDescArg"
          then rawSum (reifyType subT.S) (reifyType subF.S)
          else fallback
    else throw "reifyType: unsupported value tag '${t}'";

  # -- Value extraction (internal) --
  #
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
          extractInner elemTy elemTyVal item.d.snd.fst
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
        { _tag = "Left"; value = extractInner hoasTy.left (armTy "VTrue") val.d.snd.fst; }
      else if isDescInr val then
        { _tag = "Right"; value = extractInner hoasTy.right (armTy "VFalse") val.d.snd.fst; }
      else throw "extract: Sum value is neither inl nor inr (got ${val.tag})"

    else if t == "sigma" then
      let
        fstNix = extractInner hoasTy.fst tyVal.fst val.fst;
        sndTyVal = E.instantiate tyVal.closure val.fst;
        r = builtins.tryEval (hoasTy.body { _htag = "unit"; });
        sndHoas = if r.success then r.value else reifyType sndTyVal;
      in { fst = fstNix; snd = extractInner sndHoas sndTyVal val.snd; }

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      let
        fields = hoasTy.fields;
        n = builtins.length fields;
      in
        if n == 0 then {}
        else if n == 1 then
          { ${(builtins.head fields).name} = extractInner (builtins.head fields).type tyVal val; }
        else
          let
            extractFields = remaining: tyV: v:
              if builtins.length remaining == 1 then
                { ${(builtins.head remaining).name} = extractInner (builtins.head remaining).type tyV v; }
              else
                let
                  f = builtins.head remaining;
                  rest = builtins.tail remaining;
                  sndTyVal = E.instantiate tyV.closure v.fst;
                in
                { ${f.name} = extractInner f.type tyV.fst v.fst; }
                // extractFields rest sndTyVal v.snd;
          in extractFields fields tyVal val

    else if t == "maybe" then
      # Maybe = Sum(inner, Unit). VInl = value present, VInr = null
      if val.tag == "VInl" then extractInner hoasTy.inner tyVal.left val.val
      else if val.tag == "VInr" then null
      else throw "extract: Maybe value is neither inl nor inr (got ${val.tag})"

    else if t == "variant" then
      let
        branches = hoasTy.branches;
        extractBranch = bs: tyV: v:
          let n = builtins.length bs; in
          if n == 1 then
            { _tag = (builtins.head bs).tag; value = extractInner (builtins.head bs).type tyV v; }
          else
            let b1 = builtins.head bs; rest = builtins.tail bs; in
            if v.tag == "VInl" then
              { _tag = b1.tag; value = extractInner b1.type tyV.left v.val; }
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
            hoasArg = elaborateValue domainTy nixArg;
            kernelArg = E.eval [] (H.elab hoasArg);
            resultVal = E.instantiate val.closure kernelArg;
            codomainTyVal = E.instantiate tyVal.closure kernelArg;
            r = builtins.tryEval (hoasTy.body hoasArg);
            codomainHoas = if r.success then r.value else reifyType codomainTyVal;
          in extractInner codomainHoas codomainTyVal resultVal

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
                fieldHoas = reifyType dTy.S;
                fieldNix = extractInner fieldHoas dTy.S fieldVal;
                subDesc = E.instantiate dTy.T fieldVal;
            in [ fieldNix ] ++ extractFields subDesc rest
          else if dTy.tag == "VDescRec" then
            let recVal = pl.fst;
                rest = pl.snd;
                recNix = extractInner hoasTy tyVal recVal;
            in [ recNix ] ++ extractFields dTy.D rest
          else if dTy.tag == "VDescPi" then
            # Opaque lambda field: return the kernel VLam wrapped as a
            # Nix function via the existing pi-extract discipline. Domain
            # is reified; codomain is the outer mu's hoasTy (rec under Pi).
            let lamVal = pl.fst;
                rest = pl.snd;
                domainHoas = reifyType dTy.S;
                piHoas = H.forall "_" domainHoas (_: hoasTy);
                piTyVal = V.vPi "_" dTy.S (V.mkClosure [] (H.elab hoasTy));
                lamNix = extractInner piHoas piTyVal lamVal;
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
      then extractInner { _htag = "nat"; } tyVal val
      else if isListDesc descTyVal then
        let elemTyVal = (E.instantiate descTyVal.T V.vFalse).S;
        in extractInner { _htag = "list"; elem = reifyType elemTyVal; } tyVal val
      else if isSumDesc descTyVal then
        let leftTyVal = (E.instantiate descTyVal.T V.vTrue).S;
            rightTyVal = (E.instantiate descTyVal.T V.vFalse).S;
        in extractInner {
          _htag = "sum";
          left = reifyType leftTyVal;
          right = reifyType rightTyVal;
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
        base = reifyType tyVal;
        hoasTy' =
          if headMeta != null && (base._htag or null) == "mu"
          then base // { _dtypeMeta = headMeta; }
          else base;
      in extractInner hoasTy' tyVal val

    else throw "extract: unsupported type '${t}'";

  # -- Value extraction (public API) --
  #
  # extract : HoasTree → Val → NixValue
  # Computes kernel type value from HOAS type, then delegates to extractInner.
  extract = hoasTy: val:
    let tyVal = E.eval [] (H.elab hoasTy);
    in extractInner hoasTy tyVal val;

  # -- verifyAndExtract : HoasTree → HoasTree → NixValue --
  # Full pipeline: type-check HOAS term → eval → extract to Nix value.
  # Computes kernel type value once and uses extractInner directly.
  verifyAndExtract = hoasTy: hoasImpl:
    let
      checked = H.checkHoas hoasTy hoasImpl;
    in if checked ? error
      then throw "verifyAndExtract: type check failed"
      else
        let
          tm = H.elab hoasImpl;
          val = E.eval [] tm;
          tyVal = E.eval [] (H.elab hoasTy);
        in extractInner hoasTy tyVal val;

  # -- Decision procedure --
  #
  # decide : HoasTree → NixValue → Bool
  # Returns true iff both elaboration and kernel type-checking succeed.
  # Uses tryEval to catch elaboration throws and checks for kernel errors.
  decide = hoasTy: value:
    let
      result = builtins.tryEval (
        let
          hoasVal = elaborateValue hoasTy value;
          checked = H.checkHoas hoasTy hoasVal;
        in !(checked ? error)
      );
    in result.success && result.value;

  # -- Convenience: elaborate type then decide --
  decideType = type: value:
    decide (elaborateType type) value;

in mk {
  doc = ''
    # fx.tc.elaborate — Elaboration Bridge

    Bridges the fx.types layer to the kernel's term representation
    via the HOAS combinator layer. Provides the Nix ↔ kernel boundary.

    Spec reference: kernel-mvp-research.md §3.

    ## Type Elaboration

    - `elaborateType : FxType → Hoas` — convert an fx.types type descriptor
      to an HOAS tree. Dispatches on: (1) `_kernel` annotation, (2) structural
      fields (Pi: domain/codomain, Sigma: fstType/sndFamily), (3) name
      convention (Bool, Nat, String, Int, Float, ...).
      Dependent Pi/Sigma require explicit `_kernel` annotation.

    ## Value Elaboration

    - `elaborateValue : Hoas → NixVal → Hoas` — convert a Nix value to
      an HOAS term tree given its HOAS type. Bool→true_/false_, Int→natLit,
      List→cons chain, Sum→inl/inr, Sigma→pair. Trampolined for large lists.

    ## Structural Validation

    - `validateValue : String → Hoas → NixVal → [{ path; msg; }]` —
      applicative structural validator. Mirrors `elaborateValue`'s recursion
      but accumulates all errors instead of throwing on the first.
      Path accumulator threads structural context (Reader effect).
      Error list is the free monoid (Writer effect).
      Empty list ↔ `elaborateValue` would succeed (soundness invariant).

    ## Value Extraction

    - `extract : Hoas → Val → NixValue` — reverse of `elaborateValue`.
      Converts kernel values back to Nix values. VZero→0, VSucc^n→n,
      VCons chain→list, VInl/VInr→tagged union.
      Pi extraction wraps the VLam as a Nix function with boundary conversion.
      Opaque types (Attrs, Path, Function, Any) throw — kernel discards payloads.
    - `extractInner : Hoas → Val → Val → NixValue` — three-argument extraction
      with kernel type value threading. Supports dependent Pi/Sigma via closure
      instantiation instead of sentinel tests.
    - `reifyType : Val → Hoas` — converts a kernel type value back to HOAS.
      Fallback for when HOAS body application fails (dependent types).
      Loses sugar (VSigma→sigma, not record).

    ## Decision Procedure

    - `decide : Hoas → NixVal → Bool` — returns true iff elaboration
      and kernel type-checking both succeed. Uses `tryEval` for safety.
    - `decideType : FxType → NixVal → Bool` — elaborate type then decide.

    ## Full Pipeline

    - `verifyAndExtract : Hoas → Hoas → NixValue` — type-check an HOAS
      implementation against an HOAS type, evaluate, extract to Nix value.
      Throws on type error.
  '';
  value = {
    inherit elaborateType elaborateValue validateValue extract extractInner reifyType verifyAndExtract decide decideType;
  };
  tests = let
    FP = fx.types.primitives;
    FC = fx.types.constructors;
    FD = fx.types.dependent;
    BoolT = FP.Bool;
    IntT = FP.Int;
    UnitT = FP.Unit;
    Arrow = domType: codType:
      FD.Pi { domain = domType; codomain = _: codType;
              universe = let a = domType.universe; b = codType.universe;
                         in if a >= b then a else b; };
    Product = fstType: sndType:
      FD.Sigma { fst = fstType; snd = _: sndType;
                 universe = let a = fstType.universe; b = sndType.universe;
                            in if a >= b then a else b; };
  in {
    # -- Type elaboration: _kernel dispatch --

    "elab-type-bool" = {
      expr = (elaborateType BoolT)._htag;
      expected = "bool";
    };
    "elab-type-int" = {
      expr = (elaborateType IntT)._htag;
      expected = "int";
    };
    "elab-type-unit" = {
      expr = (elaborateType UnitT)._htag;
      expected = "unit";
    };
    # `H.listOf` and `H.sum` elaborate to app-spines of the macro's
    # polymorphic `T`. The app form preserves `_dtypeMeta` on the
    # polyField head and the parameter HOAS as literal args, which
    # `elaborateValue`/`validateValue`/`extractInner` consume directly
    # via their "app" branches. At the value level the application
    # reduces to `VMu (listDesc A)` / `VMu (sumDesc A B)`; the Tm-level
    # shape is "app".
    "elab-type-list-int" = {
      expr = (elaborateType (FC.ListOf IntT))._htag;
      expected = "app";
    };
    "elab-type-list-bool" = {
      expr = (elaborateType (FC.ListOf BoolT))._htag;
      expected = "app";
    };
    "elab-type-either" = {
      expr = (elaborateType (FC.Either IntT BoolT))._htag;
      expected = "app";
    };
    "elab-type-arrow" = {
      expr = (elaborateType (Arrow IntT BoolT))._htag;
      expected = "pi";
    };
    "elab-type-product" = {
      expr = (elaborateType (Product IntT BoolT))._htag;
      expected = "sigma";
    };
    "elab-type-u0" = {
      expr = (elaborateType (fx.types.universe.typeAt 0))._htag;
      expected = "U";
    };

    # -- Type elaboration: structural auto-detection --

    # Structural: non-dependent Pi auto-detected
    "elab-type-auto-pi" = {
      expr = let
        piT = FD.Pi { domain = BoolT; codomain = _: IntT; universe = 0; };
      in (elaborateType piT)._htag;
      expected = "pi";
    };

    # Structural: non-dependent Sigma auto-detected
    "elab-type-auto-sigma" = {
      expr = let
        sigT = FD.Sigma { fst = BoolT; snd = _: IntT; universe = 0; };
      in (elaborateType sigT)._htag;
      expected = "sigma";
    };

    # Dependent Pi (codomain uses argument) REJECTED without _kernel
    "reject-elab-dependent-pi" = {
      expr = let
        depPi = FD.Pi { domain = BoolT; codomain = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
      in (builtins.tryEval (elaborateType depPi)).success;
      expected = false;
    };

    # Dependent Sigma (snd uses argument) REJECTED without _kernel
    "reject-elab-dependent-sigma" = {
      expr = let
        depSig = FD.Sigma { fst = BoolT; snd = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
      in (builtins.tryEval (elaborateType depSig)).success;
      expected = false;
    };

    # -- Value elaboration --

    "elab-val-true" = {
      expr = (H.elab (elaborateValue H.bool true)).tag;
      expected = "true";
    };
    "elab-val-false" = {
      expr = (H.elab (elaborateValue H.bool false)).tag;
      expected = "false";
    };
    "elab-val-zero" = {
      expr = let e = H.elab (elaborateValue H.nat 0); in "${e.tag}/${e.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-val-nat-3" = {
      expr = let e = H.elab (elaborateValue H.nat 3); in "${e.tag}/${e.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-val-unit" = {
      expr = (H.elab (elaborateValue H.unit null)).tag;
      expected = "tt";
    };
    "elab-val-nil" = {
      expr = let t = H.elab (elaborateValue (H.listOf H.nat) []); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-val-cons" = {
      expr = let t = H.elab (elaborateValue (H.listOf H.nat) [0 1]); in "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-val-inl" = {
      expr = let t = H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 0; }); in
        "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/true";
    };
    "elab-val-inr" = {
      expr = let t = H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; }); in
        "${t.tag}/${t.d.fst.tag}";
      expected = "desc-con/false";
    };
    "elab-val-pair" = {
      expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; })).tag;
      expected = "pair";
    };

    "elab-val-sigma-pi-snd" = {
      expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool))) { fst = 0; snd = _: true; })).tag;
      expected = "pair";
    };

    # -- Decision procedure: positive --

    "decide-bool-true" = {
      expr = decide H.bool true;
      expected = true;
    };
    "decide-bool-false" = {
      expr = decide H.bool false;
      expected = true;
    };
    "decide-nat-0" = {
      expr = decide H.nat 0;
      expected = true;
    };
    "decide-nat-5" = {
      expr = decide H.nat 5;
      expected = true;
    };
    "decide-unit" = {
      expr = decide H.unit null;
      expected = true;
    };
    "decide-list-empty" = {
      expr = decide (H.listOf H.nat) [];
      expected = true;
    };
    "decide-list-nat" = {
      expr = decide (H.listOf H.nat) [0 1 2];
      expected = true;
    };
    "decide-sum-left" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = 0; };
      expected = true;
    };
    "decide-sum-right" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Right"; value = true; };
      expected = true;
    };
    "decide-product" = {
      expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; };
      expected = true;
    };

    # -- Decision procedure: negative --

    "decide-bool-rejects-int" = {
      expr = decide H.bool 42;
      expected = false;
    };
    "decide-nat-rejects-neg" = {
      expr = decide H.nat (-1);
      expected = false;
    };
    "decide-nat-rejects-string" = {
      expr = decide H.nat "hello";
      expected = false;
    };
    "decide-list-rejects-wrong-elem" = {
      expr = decide (H.listOf H.nat) [true];
      expected = false;
    };
    "decide-sum-rejects-wrong-val" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = true; };
      expected = false;
    };
    "decide-product-rejects-wrong-fst" = {
      expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = true; snd = true; };
      expected = false;
    };

    # -- Decision procedure: record totality --

    "decide-record-rejects-missing-field" = {
      expr = decide (H.record [{ name = "n"; type = H.int_; }]) { x = 1; };
      expected = false;
    };
    "decide-record-rejects-non-attrset" = {
      expr = decide (H.record [{ name = "n"; type = H.int_; }]) 42;
      expected = false;
    };
    "decide-record-rejects-partial-fields" = {
      expr = decide (H.record [{ name = "a"; type = H.int_; } { name = "b"; type = H.bool; }]) { a = 1; };
      expected = false;
    };
    "decide-record-accepts-complete" = {
      expr = decide (H.record [{ name = "a"; type = H.int_; } { name = "b"; type = H.bool; }]) { a = 1; b = true; };
      expected = true;
    };

    # Stack safety: full pipeline (elaborate → eval → check) trampolined for cons.
    # Elements are all `0` (Peano depth 1) to isolate the cons-chain stressor —
    # matches the convention of the four sibling "5000" stress tests in
    # hoas/check/conv/quote. Under μnatDesc, `natLit k` is O(k) Peano depth by
    # design, so varying-magnitude elements would conflate two orthogonal
    # stressors. See `decide-nat-1000` below for the dedicated Peano-depth test.
    "decide-list-5000" = {
      expr = decide (H.listOf H.nat) (builtins.genList (_: 0) 5000);
      expected = true;
    };

    # Names the shared-D fast path on the desc-con trampoline: H.cons
    # emits a single dTm at elab time, so node.D == tm.D is structural-
    # equal across layers and the peel short-circuits before reaching
    # the conv-equality fallback.
    "decide-list-5000-shared-d" = {
      expr = decide (H.listOf H.nat) (builtins.genList (_: 0) 5000);
      expected = true;
    };

    # Stack safety: full pipeline on a deep Peano literal. Under μnatDesc
    # representation `natLit N` is an N-deep desc-con chain; this test exercises
    # the desc-con trampolines in elaborate/check/eval end-to-end. Bound chosen
    # so the test stays well under a second on commodity hardware — higher
    # bounds are meaningful but dominated by memory allocation, not correctness.
    "decide-nat-1000" = {
      expr = decide H.nat 1000;
      expected = true;
    };

    # 5000-element list via the macro-generated ListDT.cons rather than
    # H.cons. Each layer is a β-redex reducing to `desc-con D payload` at
    # eval time; the desc-con trampoline identifies shared D across layers
    # via conv-equality when structural == doesn't hold, and decomposes
    # each layer's payload using linearProfile on the cons-branch
    # description (Just [A], one head and a rec tail).
    "decide-list-5000-macro" = {
      expr = let
        L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "nil"  [])
            (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
          ]);
        nilA = H.app L.nil H.nat;
        consA = h: t: H.app (H.app (H.app L.cons H.nat) h) t;
        build = builtins.foldl' (acc: _: consA H.zero acc)
          nilA (builtins.genList (x: x) 5000);
        hoasTy = H.app L.T H.nat;
        result = H.checkHoas hoasTy build;
      in !(result ? error);
      expected = true;
    };

    # 1000-deep Peano chain via the macro-generated NatDT.succ rather
    # than H.succ. Each constructor cascade β-reduces at eval time; the
    # desc-con trampoline peels via linearProfile at Just [] (0 data
    # fields, rec tail), matching the succ-branch description shape.
    "decide-nat-1000-macro" = {
      expr = let
        N = H.datatype "Nat" [
          (H.con "zero" [])
          (H.con "succ" [ (H.recField "pred") ])
        ];
        build = builtins.foldl' (acc: _: H.app N.succ acc)
          N.zero (builtins.genList (x: x) 1000);
        result = H.checkHoas N.T build;
      in !(result ? error);
      expected = true;
    };


    # Dependent sigma: body produces "eq" which elaborateValue can't handle
    "decide-dep-sigma-rejected" = {
      expr = decide (H.sigma "x" H.nat (x: H.eq H.nat x H.zero)) { fst = 0; snd = null; };
      expected = false;
    };

    # -- HOAS substitution: dependent Sigma via body(fstHoas) --

    # Non-dependent Sigma: HOAS substitution produces same result as before
    "elab-dep-sigma-non-dep-baseline" = {
      expr = let
        ty = H.sigma "x" H.nat (_: H.bool);
        val = { fst = 0; snd = true; };
      in (H.elab (elaborateValue ty val)).tag;
      expected = "pair";
    };

    # Dependent Sigma whose body produces an elaboratable type
    "elab-dep-sigma-snd-type-correct" = {
      expr = let
        # Sigma(x: Bool). if x then Nat else Bool
        # body(true_) = Nat, so snd = 42 should elaborate as Nat
        ty = H.sigma "x" H.bool (x:
          let t = (H.elab x).tag; in
          if t == "true" then H.nat
          else if t == "false" then H.bool
          else H.nat);
        val = { fst = true; snd = 42; };
      in (H.elab (elaborateValue ty val)).tag;
      expected = "pair";
    };

    # Dependent Sigma kernel-checks: elaborated pair passes checkHoas
    "elab-dep-sigma-kernel-checks" = {
      expr = let
        ty = H.sigma "x" H.bool (x:
          let t = (H.elab x).tag; in
          if t == "true" then H.nat
          else if t == "false" then H.bool
          else H.nat);
        val = { fst = true; snd = 42; };
        hoasVal = elaborateValue ty val;
        checked = H.checkHoas ty hoasVal;
      in !(checked ? error);
      expected = true;
    };

    # Dependent Sigma roundtrip: elaborate -> check -> eval -> extract = original
    "elab-dep-sigma-roundtrip" = {
      expr = let
        ty = H.sigma "x" H.nat (_: H.bool);
        val = { fst = 5; snd = true; };
      in extract ty (E.eval [] (H.elab (elaborateValue ty val)));
      expected = { fst = 5; snd = true; };
    };

    # Dependent Sigma: wrong snd type rejected via substituted body
    "elab-dep-sigma-snd-mismatch" = {
      expr = let
        ty = H.sigma "x" H.bool (x:
          let t = (H.elab x).tag; in
          if t == "true" then H.nat
          else H.bool);
        # fst=true means snd should be Nat, but we pass a bool
        val = { fst = true; snd = false; };
      in decide ty val;
      expected = false;
    };

    # validateValue: dependent Sigma validates correctly
    "validate-dep-sigma-valid" = {
      expr = let
        ty = H.sigma "x" H.bool (x:
          let t = (H.elab x).tag; in
          if t == "true" then H.nat
          else H.bool);
        val = { fst = true; snd = 42; };
      in validateValue "$" ty val;
      expected = [];
    };

    # validateValue: dependent Sigma reports snd errors
    "validate-dep-sigma-snd-error" = {
      expr = let
        ty = H.sigma "x" H.bool (x:
          let t = (H.elab x).tag; in
          if t == "true" then H.nat
          else H.bool);
        # fst=true → snd should be Nat, but we pass a string
        val = { fst = true; snd = "wrong"; };
        errors = validateValue "$" ty val;
      in builtins.length errors > 0;
      expected = true;
    };

    # -- Pi opaque elaboration: function values at Pi types --

    # Raw Nix function at Pi type → opaque lambda
    "elab-pi-opaque-lambda" = {
      expr = let
        ty = H.forall "x" H.nat (_: H.bool);
        hoasVal = elaborateValue ty (x: x > 0);
      in (H.elab hoasVal).tag;
      expected = "opaque-lam";
    };

    # Verified value with _hoasImpl → uses HOAS term directly
    "elab-pi-verified-uses-hoasImpl" = {
      expr = let
        ty = H.forall "x" H.nat (_: H.nat);
        verified = { _hoasImpl = H.lam "x" H.nat (x: x); __functor = self: x: x; };
        hoasVal = elaborateValue ty verified;
      in (H.elab hoasVal).tag;
      expected = "lam";
    };

    # Opaque lambda at Pi type → kernel check passes (domain matches)
    "elab-pi-domain-check" = {
      expr = let
        ty = H.forall "x" H.nat (_: H.bool);
        hoasVal = elaborateValue ty (x: x > 0);
        checked = H.checkHoas ty hoasVal;
      in !(checked ? error);
      expected = true;
    };

    # Function at wrong Pi domain → kernel check fails
    "elab-pi-domain-mismatch" = {
      expr = let
        ty = H.forall "x" H.nat (_: H.bool);
        wrongTy = H.forall "x" H.bool (_: H.bool);
        hoasVal = elaborateValue wrongTy (x: x);
        # Check against nat-domain Pi, but elaborated against bool-domain Pi
        checked = H.checkHoas ty hoasVal;
      in checked ? error;
      expected = true;
    };

    # Non-function value at Pi type → throws
    "elab-pi-non-function-rejects" = {
      expr = (builtins.tryEval (elaborateValue (H.forall "x" H.nat (_: H.nat)) 42)).success;
      expected = false;
    };

    # Opaque Pi roundtrip: elaborate → check → eval → extract = original function
    "extract-opaque-pi-roundtrip" = {
      expr = let
        ty = H.forall "x" H.nat (_: H.nat);
        f = x: x + 1;
        hoasVal = elaborateValue ty f;
        checked = H.checkHoas ty hoasVal;
        val = E.eval [] (H.elab hoasVal);
        extracted = extract ty val;
      in extracted 5;
      expected = 6;
    };

    # decide returns true for valid Pi function
    "decide-pi-with-kernel-accepts" = {
      expr = decide (H.forall "x" H.nat (_: H.bool)) (x: x > 0);
      expected = true;
    };

    # decide rejects non-function at Pi type
    "decide-pi-rejects-non-function" = {
      expr = decide (H.forall "x" H.nat (_: H.nat)) 42;
      expected = false;
    };

    # validateValue: Pi accepts function
    "validate-pi-accepts-function" = {
      expr = validateValue "$" (H.forall "x" H.nat (_: H.nat)) (x: x + 1);
      expected = [];
    };

    # validateValue: Pi rejects non-function
    "validate-pi-rejects-non-function" = {
      expr = builtins.length (validateValue "$" (H.forall "x" H.nat (_: H.nat)) 42) > 0;
      expected = true;
    };

    # -- Regression: decide(T,v) == T.check(v) --

    "regression-bool-true" = {
      expr = (decideType BoolT true) == (BoolT.check true);
      expected = true;
    };
    "regression-bool-rejects-int" = {
      expr = (decideType BoolT 42) == (BoolT.check 42);
      expected = true;
    };
    "regression-int-42" = {
      expr = (decideType IntT 42) == (IntT.check 42);
      expected = true;
    };
    "regression-int-rejects-string" = {
      expr = (decideType IntT "x") == (IntT.check "x");
      expected = true;
    };
    "regression-unit-null" = {
      expr = (decideType UnitT null) == (UnitT.check null);
      expected = true;
    };
    "regression-unit-rejects-42" = {
      expr = (decideType UnitT 42) == (UnitT.check 42);
      expected = true;
    };
    "regression-list-int-valid" = {
      expr = let lt = FC.ListOf IntT; in (decideType lt [0 1 2]) == (lt.check [0 1 2]);
      expected = true;
    };
    "regression-list-int-empty" = {
      expr = let lt = FC.ListOf IntT; in (decideType lt []) == (lt.check []);
      expected = true;
    };
    "regression-list-int-rejects-bad" = {
      expr = let lt = FC.ListOf IntT; in (decideType lt [true]) == (lt.check [true]);
      expected = true;
    };
    "regression-either-left-valid" = {
      expr = let et = FC.Either IntT BoolT; v = { _tag = "Left"; value = 0; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "regression-either-right-bad" = {
      expr = let et = FC.Either IntT BoolT; v = { _tag = "Right"; value = 42; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "regression-product-valid" = {
      expr = let pt = Product IntT BoolT; v = { fst = 0; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };
    "regression-product-bad-fst" = {
      expr = let pt = Product IntT BoolT; v = { fst = true; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };

    # -- Primitive type elaboration: name-based auto-detection --

    "elab-type-auto-string" = {
      expr = (elaborateType FP.String)._htag;
      expected = "string";
    };
    "elab-type-auto-int" = {
      expr = (elaborateType FP.Int)._htag;
      expected = "int";
    };
    "elab-type-auto-float" = {
      expr = (elaborateType FP.Float)._htag;
      expected = "float";
    };
    "elab-type-auto-attrs" = {
      expr = (elaborateType FP.Attrs)._htag;
      expected = "attrs";
    };
    "elab-type-auto-path" = {
      expr = (elaborateType FP.Path)._htag;
      expected = "path";
    };
    "elab-type-auto-function" = {
      expr = (elaborateType FP.Function)._htag;
      expected = "function";
    };
    "elab-type-auto-any" = {
      expr = (elaborateType FP.Any)._htag;
      expected = "any";
    };

    # -- Value elaboration: primitives --

    "elab-val-string" = {
      expr = (H.elab (elaborateValue H.string "hello")).tag;
      expected = "string-lit";
    };
    "elab-val-string-value" = {
      expr = (H.elab (elaborateValue H.string "hello")).value;
      expected = "hello";
    };
    "elab-val-int" = {
      expr = (H.elab (elaborateValue H.int_ 42)).tag;
      expected = "int-lit";
    };
    "elab-val-float" = {
      expr = (H.elab (elaborateValue H.float_ 3.14)).tag;
      expected = "float-lit";
    };
    "elab-val-attrs" = {
      expr = (H.elab (elaborateValue H.attrs { x = 1; })).tag;
      expected = "attrs-lit";
    };
    "elab-val-fn" = {
      expr = (H.elab (elaborateValue H.function_ (x: x))).tag;
      expected = "fn-lit";
    };
    "elab-val-any-string" = {
      expr = (H.elab (elaborateValue H.any "anything")).tag;
      expected = "any-lit";
    };
    "elab-val-any-int" = {
      expr = (H.elab (elaborateValue H.any 42)).tag;
      expected = "any-lit";
    };

    # -- Decision procedure: primitive positives --

    "decide-string-hello" = {
      expr = decide H.string "hello";
      expected = true;
    };
    "decide-string-empty" = {
      expr = decide H.string "";
      expected = true;
    };
    "decide-int-42" = {
      expr = decide H.int_ 42;
      expected = true;
    };
    "decide-int-neg" = {
      expr = decide H.int_ (-10);
      expected = true;
    };
    "decide-float-pi" = {
      expr = decide H.float_ 3.14;
      expected = true;
    };
    "decide-attrs-set" = {
      expr = decide H.attrs { x = 1; y = 2; };
      expected = true;
    };
    "decide-fn-id" = {
      expr = decide H.function_ (x: x);
      expected = true;
    };
    "decide-any-string" = {
      expr = decide H.any "anything";
      expected = true;
    };
    "decide-any-int" = {
      expr = decide H.any 42;
      expected = true;
    };
    "decide-any-null" = {
      expr = decide H.any null;
      expected = true;
    };

    # -- Decision procedure: primitive negatives --

    "decide-string-rejects-int" = {
      expr = decide H.string 42;
      expected = false;
    };
    "decide-int-rejects-string" = {
      expr = decide H.int_ "hello";
      expected = false;
    };
    "decide-float-rejects-int" = {
      expr = decide H.float_ 42;
      expected = false;
    };
    "decide-attrs-rejects-list" = {
      expr = decide H.attrs [1 2];
      expected = false;
    };
    "decide-fn-rejects-string" = {
      expr = decide H.function_ "hello";
      expected = false;
    };

    # -- Extraction: roundtrip tests --
    # Roundtrip: extract(T, eval(elab(elaborateValue(T, v)))) == v

    "extract-nat-0" = {
      expr = extract H.nat (E.eval [] (H.elab (elaborateValue H.nat 0)));
      expected = 0;
    };
    "extract-nat-5" = {
      expr = extract H.nat (E.eval [] (H.elab (elaborateValue H.nat 5)));
      expected = 5;
    };
    "extract-bool-true" = {
      expr = extract H.bool (E.eval [] (H.elab (elaborateValue H.bool true)));
      expected = true;
    };
    "extract-bool-false" = {
      expr = extract H.bool (E.eval [] (H.elab (elaborateValue H.bool false)));
      expected = false;
    };
    "extract-unit" = {
      expr = extract H.unit (E.eval [] (H.elab (elaborateValue H.unit null)));
      expected = null;
    };
    "extract-string" = {
      expr = extract H.string (E.eval [] (H.elab (elaborateValue H.string "hello")));
      expected = "hello";
    };
    "extract-int" = {
      expr = extract H.int_ (E.eval [] (H.elab (elaborateValue H.int_ 42)));
      expected = 42;
    };
    "extract-float" = {
      expr = extract H.float_ (E.eval [] (H.elab (elaborateValue H.float_ 3.14)));
      expected = 3.14;
    };
    "extract-list-empty" = {
      expr = extract (H.listOf H.nat) (E.eval [] (H.elab (elaborateValue (H.listOf H.nat) [])));
      expected = [];
    };
    "extract-list-nat" = {
      expr = extract (H.listOf H.nat) (E.eval [] (H.elab (elaborateValue (H.listOf H.nat) [1 2 3])));
      expected = [1 2 3];
    };
    "extract-sum-left" = {
      expr = extract (H.sum H.nat H.bool) (E.eval [] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 42; })));
      expected = { _tag = "Left"; value = 42; };
    };
    "extract-sum-right" = {
      expr = extract (H.sum H.nat H.bool) (E.eval [] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; })));
      expected = { _tag = "Right"; value = true; };
    };
    "extract-sigma" = {
      expr = let ty = H.sigma "x" H.nat (_: H.bool); in
        extract ty (E.eval [] (H.elab (elaborateValue ty { fst = 5; snd = true; })));
      expected = { fst = 5; snd = true; };
    };

    "extract-sigma-pi-snd" = {
      expr = let
        ty = H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool));
        hoasVal = H.pair (H.ann H.zero H.nat) (H.lam "y" H.nat (_: H.true_));
        val = E.eval [] (H.elab hoasVal);
        result = extract ty val;
      in (result.snd 0);
      expected = true;
    };

    # -- Extraction: Pi (verified function) --

    "extract-pi-identity" = {
      # Identity function: λ(x:Nat).x → extract → call with 5
      expr = let
        fnTy = H.forall "x" H.nat (_: H.nat);
        idFn = H.lam "x" H.nat (x: x);
        val = E.eval [] (H.elab idFn);
        nixFn = extract fnTy val;
      in nixFn 5;
      expected = 5;
    };
    "extract-pi-const" = {
      # Constant function: λ(x:Bool).0 → extract → call with true
      expr = let
        fnTy = H.forall "x" H.bool (_: H.nat);
        constFn = H.lam "x" H.bool (_: H.zero);
        val = E.eval [] (H.elab constFn);
        nixFn = extract fnTy val;
      in nixFn true;
      expected = 0;
    };

    # -- verifyAndExtract pipeline --

    "verify-extract-nat" = {
      expr = verifyAndExtract H.nat (H.natLit 7);
      expected = 7;
    };
    "verify-extract-bool" = {
      expr = verifyAndExtract H.bool H.true_;
      expected = true;
    };
    "verify-extract-fn" = {
      # Full pipeline: write function in HOAS → verify → extract → call
      expr = let
        fnTy = H.forall "x" H.nat (_: H.nat);
        fnImpl = H.lam "x" H.nat (x: x);
        nixFn = verifyAndExtract fnTy fnImpl;
      in nixFn 10;
      expected = 10;
    };
    "verify-extract-type-error" = {
      # Type error: Bool term against Nat type → throws
      expr = (builtins.tryEval (verifyAndExtract H.nat H.true_)).success;
      expected = false;
    };

    # -- Extraction: stack safety --

    "extract-list-5000" = {
      # Stack safety: extract a 5000-element list (booleans for O(1) per element)
      expr = builtins.length (
        extract (H.listOf H.bool)
          (E.eval [] (H.elab (elaborateValue (H.listOf H.bool)
            (builtins.genList (_: true) 5000))))
      );
      expected = 5000;
    };

    # -- Extraction: opaque types throw --

    "extract-attrs-throws" = {
      expr = (builtins.tryEval (extract H.attrs (E.eval [] (H.elab (elaborateValue H.attrs { x = 1; }))))).success;
      expected = false;
    };
    "extract-fn-throws" = {
      expr = (builtins.tryEval (extract H.function_ (E.eval [] (H.elab (elaborateValue H.function_ (x: x)))))).success;
      expected = false;
    };

    # -- Extraction: macro-generated datatypes (mu-branch + app-branch) --
    # Macro-generated datatypes elaborate to HOAS types whose surface tag
    # is "mu" (monomorphic) or "app" (polymorphic instantiation). The
    # extractInner mu-branch detects prelude-equivalent shapes and routes
    # to the same Nix output as the nat/list/sum/bool/unit branches; other
    # shapes decompose generically into a constructor record `{ _con =
    # "<name>"; <field> = ...; }` using `_dtypeMeta` attached to the
    # macro's `T`. The app-branch peels the spine to the macro head,
    # recovers `_dtypeMeta`, and reduces the type via reifyType.

    "extract-mu-unit-tt" = {
      expr = let
        U = H.datatype "Unit" [ (H.con "tt" []) ];
      in extract U.T (E.eval [] (H.elab U.tt));
      expected = null;
    };
    "extract-mu-bool-true" = {
      expr = let
        B = H.datatype "Bool" [ (H.con "true" []) (H.con "false" []) ];
      in extract B.T (E.eval [] (H.elab (builtins.getAttr "true" B)));
      expected = true;
    };
    "extract-mu-bool-false" = {
      expr = let
        B = H.datatype "Bool" [ (H.con "true" []) (H.con "false" []) ];
      in extract B.T (E.eval [] (H.elab (builtins.getAttr "false" B)));
      expected = false;
    };
    "extract-mu-nat-zero" = {
      expr = let
        N = H.datatype "Nat" [
          (H.con "zero" [])
          (H.con "succ" [ (H.recField "pred") ])
        ];
      in extract N.T (E.eval [] (H.elab N.zero));
      expected = 0;
    };
    "extract-mu-nat-3" = {
      expr = let
        N = H.datatype "Nat" [
          (H.con "zero" [])
          (H.con "succ" [ (H.recField "pred") ])
        ];
        three = H.app N.succ (H.app N.succ (H.app N.succ N.zero));
      in extract N.T (E.eval [] (H.elab three));
      expected = 3;
    };

    # Polymorphic via app: extract on `app (app ListDT.T nat)` peels the
    # app spine, recovers `_dtypeMeta` from the polyField head, and
    # delegates to the mu-branch with the reduced VMu kernel type.
    "extract-app-list-empty" = {
      expr = let
        L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "nil"  [])
            (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
          ]);
        Tnat = H.app L.T H.nat;
        nilNat = H.app L.nil H.nat;
      in extract Tnat (E.eval [] (H.elab nilNat));
      expected = [];
    };
    "extract-app-list-3" = {
      expr = let
        L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "nil"  [])
            (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
          ]);
        Tnat = H.app L.T H.nat;
        nilNat = H.app L.nil H.nat;
        consNat = h: t: H.app (H.app (H.app L.cons H.nat) h) t;
        l = consNat H.zero (consNat (H.succ H.zero) (consNat (H.succ (H.succ H.zero)) nilNat));
      in extract Tnat (E.eval [] (H.elab l));
      expected = [ 0 1 2 ];
    };
    "extract-app-sum-left" = {
      expr = let
        S = H.datatypeP "Sum"
          [ { name = "A"; kind = H.u 0; } { name = "B"; kind = H.u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (H.con "inl" [ (H.field "value" A) ])
            (H.con "inr" [ (H.field "value" B) ])
          ]);
        Tnb = H.app (H.app S.T H.nat) H.bool;
        v = H.app (H.app (H.app S.inl H.nat) H.bool) H.zero;
      in extract Tnb (E.eval [] (H.elab v));
      expected = { _tag = "Left"; value = 0; };
    };
    "extract-app-sum-right" = {
      expr = let
        S = H.datatypeP "Sum"
          [ { name = "A"; kind = H.u 0; } { name = "B"; kind = H.u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (H.con "inl" [ (H.field "value" A) ])
            (H.con "inr" [ (H.field "value" B) ])
          ]);
        Tnb = H.app (H.app S.T H.nat) H.bool;
        v = H.app (H.app (H.app S.inr H.nat) H.bool) H.true_;
      in extract Tnb (E.eval [] (H.elab v));
      expected = { _tag = "Right"; value = true; };
    };

    # Generic decomposition for non-prelude shapes (TreeDT). Returns a
    # constructor record carrying the macro-supplied constructor and field
    # names from `_dtypeMeta`. Recursive fields recurse into the same outer
    # hoasTy; data fields recurse via reifyType on the kernel field type.
    "extract-mu-tree-leaf" = {
      expr = let
        Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "leaf" [ (H.field "value" A) ])
            (H.con "node" [ (H.recField "left") (H.recField "right") ])
          ]);
        Tnat = H.app Tree.T H.nat;
        v = H.app (H.app Tree.leaf H.nat) (H.succ H.zero);
      in extract Tnat (E.eval [] (H.elab v));
      expected = { _con = "leaf"; value = 1; };
    };
    "extract-mu-tree-node" = {
      expr = let
        Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "leaf" [ (H.field "value" A) ])
            (H.con "node" [ (H.recField "left") (H.recField "right") ])
          ]);
        Tnat = H.app Tree.T H.nat;
        leafZero = H.app (H.app Tree.leaf H.nat) H.zero;
        leafOne  = H.app (H.app Tree.leaf H.nat) (H.succ H.zero);
        v = H.app (H.app (H.app Tree.node H.nat) leafZero) leafOne;
      in extract Tnat (E.eval [] (H.elab v));
      expected = {
        _con = "node";
        left  = { _con = "leaf"; value = 0; };
        right = { _con = "leaf"; value = 1; };
      };
    };

    # reifyType for non-prelude VMu shapes: returns an `H.mu D'` form
    # rather than throwing. Exercises the description-driven fallback —
    # no metadata recovery from kernel D alone, so the result is anonymous;
    # extractInner's "mu" branch handles the decomposition downstream when
    # callers attach `_dtypeMeta` to the surface hoasTy.
    "reify-mu-unit-shape" = {
      expr = let
        U = H.datatype "Unit" [ (H.con "tt" []) ];
        tyVal = E.eval [] (H.elab U.T);
      in (reifyType tyVal)._htag;
      expected = "mu";
    };
    "reify-mu-bool-shape" = {
      expr = let
        B = H.datatype "Bool" [ (H.con "true" []) (H.con "false" []) ];
        tyVal = E.eval [] (H.elab B.T);
      in (reifyType tyVal)._htag;
      expected = "mu";
    };

    # -- Cross-cutting integration tests --
    # Compound types mixing polarity, refinement, and dependent fields.
    # Each verifies that conjunction (kernelDecide ∧ guard) runs both paths.

    # Record(Pi, Sigma(refined)): mixed polarity compound type
    "integration-record-pi-sigma-refined" = {
      expr = let
        refined = fx.types.refinement.refined;
        PosInt = refined "PosInt" IntT (x: builtins.isInt x && x > 0);
        schema = {
          transform = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
          pair = FD.Sigma { fst = PosInt; snd = _: BoolT; universe = 0; };
        };
        RT = FC.Record schema;
        good = { transform = x: x + 1; pair = { fst = 5; snd = true; }; };
        badPair = { transform = x: x + 1; pair = { fst = -1; snd = true; }; };
        badFn = { transform = 42; pair = { fst = 5; snd = true; }; };
      in RT.check good && !(RT.check badPair) && !(RT.check badFn);
      expected = true;
    };

    # Record(Pi, Sigma(refined)): diagnose shows conjunction
    "integration-record-pi-sigma-diagnose" = {
      expr = let
        refined = fx.types.refinement.refined;
        PosInt = refined "PosInt" IntT (x: builtins.isInt x && x > 0);
        schema = {
          transform = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
          pair = FD.Sigma { fst = PosInt; snd = _: BoolT; universe = 0; };
        };
        RT = FC.Record schema;
        d = RT.diagnose { transform = x: x + 1; pair = { fst = 5; snd = true; }; };
      in d.kernel && d.agreement;
      expected = true;
    };

    # Maybe(DepRecord(dependent ListOf)): nested dependent conjunction
    "integration-maybe-deprecord-listof" = {
      expr = let
        mkType = fx.types.foundation.mkType;
        SizedList = FD.DepRecord [
          { name = "n"; type = IntT; }
          { name = "items"; type = self:
              mkType {
                name = "List[n=${toString self.n}]";
                kernelType = H.any;
                guard = v: builtins.isList v && builtins.length v == self.n;
              };
          }
        ];
        MT = FC.Maybe SizedList;
      in MT.check null
         && MT.check { fst = 3; snd = [1 2 3]; }
         && !(MT.check { fst = 3; snd = [1 2]; })
         && !(MT.check "not-a-pair");
      expected = true;
    };

    # ListOf(Pi): list of opaque Pi functions, kernel checks domain
    "integration-listof-pi" = {
      expr = let
        FnType = FD.Pi { domain = IntT; codomain = _: BoolT; universe = 0; };
        LT = FC.ListOf FnType;
        good = [ (x: x > 0) (x: x == 0) ];
        bad = [ (x: x > 0) 42 ];
      in LT.check good && !(LT.check bad) && LT.check [];
      expected = true;
    };

    # ListOf(Pi): kernel rejects non-function in list
    "integration-listof-pi-rejects-non-fn" = {
      expr = let
        FnType = FD.Pi { domain = IntT; codomain = _: BoolT; universe = 0; };
        LT = FC.ListOf FnType;
        d = LT.diagnose [ 42 ];
      in d.kernel == false;
      expected = true;
    };

    # Either(Sigma, Pi): sum of positive and negative types
    "integration-either-sigma-pi" = {
      expr = let
        SigT = FD.Sigma { fst = IntT; snd = _: BoolT; universe = 0; };
        PiT = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        ET = FC.Either SigT PiT;
        goodLeft = { _tag = "Left"; value = { fst = 42; snd = true; }; };
        goodRight = { _tag = "Right"; value = x: x + 1; };
        badLeft = { _tag = "Left"; value = { fst = "bad"; snd = true; }; };
        badRight = { _tag = "Right"; value = 42; };
      in ET.check goodLeft && ET.check goodRight
         && !(ET.check badLeft) && !(ET.check badRight);
      expected = true;
    };

    # Either(Sigma, Pi): diagnose shows conjunction on both branches
    "integration-either-sigma-pi-diagnose" = {
      expr = let
        SigT = FD.Sigma { fst = IntT; snd = _: BoolT; universe = 0; };
        PiT = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        ET = FC.Either SigT PiT;
        dLeft = ET.diagnose { _tag = "Left"; value = { fst = 42; snd = true; }; };
        dRight = ET.diagnose { _tag = "Right"; value = x: x + 1; };
      in dLeft.kernel && dLeft.agreement && dRight.kernel && dRight.agreement;
      expected = true;
    };
  };
}
