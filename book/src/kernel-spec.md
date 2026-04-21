# Formal Specification: Type-Checking Kernel

This document is the contract the implementation must satisfy. Every
typing rule, compute rule, and conversion rule is stated precisely.
Every test is derived from this spec. Every invariant the kernel must
maintain is listed.

The spec uses standard type-theoretic notation. No Nix code appears
here — this document is reviewable by anyone who reads dependent type
theory, regardless of implementation language.

---

## 1. Trust Model

The kernel has three layers with strictly decreasing trust requirements.

**Layer 0 — Trusted Computing Base (TCB).** The evaluator, quotation,
and conversion checker. Pure functions. No side effects. No imports
from the effect system. Bugs here compromise soundness. Every line
must be auditable.

- `eval : Env × Tm → Val`
- `quote : ℕ × Val → Tm`
- `conv : ℕ × Val × Val → Bool`

**Layer 1 — Semi-trusted.** The bidirectional type checker. Uses the
TCB and sends effects for error reporting. Bugs here may produce wrong
error messages or reject valid terms, but cannot cause unsoundness
(the TCB rejects ill-typed terms independently).

- `check : Ctx × Tm × Val → Tm`
- `infer : Ctx × Tm → Tm × Val`
- `checkTypeLevel : Ctx × Tm → Tm × ℕ`

**Layer 2 — Untrusted.** The elaborator. Translates surface syntax
(named variables, implicit arguments, level inference, eta-insertion)
into fully explicit core terms. Can have arbitrary bugs without
compromising safety — the kernel verifies the output.

### Failure modes

| Condition | Response | Rationale |
|-----------|----------|-----------|
| Kernel invariant violation | `throw` (crash) | TCB may be buggy; cannot trust own output |
| User type error | Effect `typeError` | Normal operation; handler decides policy |
| Normalization budget exceeded | `throw` (crash) | Layer 0 has no effect access; `tryEval` catches it |
| Unknown term tag | `throw` (crash) | Exhaustiveness violation = kernel bug |

---

## 2. Syntax

### 2.1 Terms (Tm)

The core term language. All binding uses de Bruijn indices. Name
annotations are cosmetic (for error messages only).

```
Tm ::=
  -- Variables and binding
  | Var(i : ℕ)                             -- de Bruijn index
  | Let(n : Name, A : Tm, t : Tm, u : Tm)  -- let n : A = t in u

  -- Functions
  | Pi(n : Name, A : Tm, B : Tm)       -- Π(n : A). B
  | Lam(n : Name, A : Tm, t : Tm)      -- λ(n : A). t
  | App(t : Tm, u : Tm)                -- t u

  -- Pairs
  | Sigma(n : Name, A : Tm, B : Tm)     -- Σ(n : A). B
  | Pair(a : Tm, b : Tm, T : Tm)        -- (a, b) as T
  | Fst(t : Tm)                         -- π₁ t
  | Snd(t : Tm)                         -- π₂ t

  -- Natural numbers
  | Nat                                 -- ℕ
  | Zero                                -- 0
  | Succ(t : Tm)                        -- S t
  | NatElim(P : Tm, z : Tm, s : Tm, n : Tm)
    -- elim_ℕ(P, z, s, n)

  -- Lists
  | List(A : Tm)                        -- List A
  | Nil(A : Tm)                         -- nil_A
  | Cons(A : Tm, h : Tm, t : Tm)        -- cons_A h t
  | ListElim(A : Tm, P : Tm, n : Tm, c : Tm, l : Tm)
    -- elim_List(A, P, n, c, l)

  -- Unit
  | Unit                                -- ⊤
  | Tt                                  -- tt

  -- Sum
  | Sum(A : Tm, B : Tm)                -- A + B
  | Inl(A : Tm, B : Tm, t : Tm)        -- inl t
  | Inr(A : Tm, B : Tm, t : Tm)        -- inr t
  | SumElim(A : Tm, B : Tm, P : Tm, l : Tm, r : Tm, s : Tm)
    -- elim_+(A, B, P, l, r, s)

  -- Identity
  | Eq(A : Tm, a : Tm, b : Tm)         -- Id_A(a, b)
  | Refl                                -- refl
  | J(A : Tm, a : Tm, P : Tm, pr : Tm, b : Tm, eq : Tm)
    -- J(A, a, P, pr, b, eq)

  -- Universes
  | U(i : ℕ)                           -- Type_i

  -- Annotations
  | Ann(t : Tm, A : Tm)                -- (t : A)

  -- Axiomatized primitive types
  | String                              -- string type
  | Int                                 -- integer type
  | Float                               -- float type
  | Attrs                               -- attribute set type
  | Path                                -- path type
  | Function                            -- opaque function type
  | Any                                 -- dynamic/any type

  -- String operations
  | StrEq(lhs : Tm, rhs : Tm)          -- string equality: lhs == rhs → H.bool (derived)

  -- Primitive literals
  | StringLit(s)                        -- string literal
  | IntLit(n)                           -- integer literal
  | FloatLit(f)                         -- float literal
  | AttrsLit                            -- attribute set literal
  | PathLit                             -- path literal
  | FnLit                               -- opaque function literal
  | AnyLit                              -- any literal

```

### 2.2 Binding convention

In `Pi(n, A, B)`, `Lam(n, A, t)`, `Sigma(n, A, B)`, and `Let(n, A, t, u)`:
the body (`B`, `t`, or `u`) binds one variable. Index 0 in the body
refers to the bound variable. All other indices shift by 1.

In `NatElim(P, z, s, n)`: `P` binds 0 variables (it's a function
term `ℕ → U`). `z` binds 0 variables. `s` binds 0 variables (it's
a function term). `n` binds 0 variables.

All eliminators take their arguments as closed terms (no implicit
binding). The motive is a function term, not a binder.

### 2.3 De Bruijn index conventions

Indices count inward from the use site: 0 = most recent binder.

Example: `λ(x : A). λ(y : B). x` is `Lam(x, A, Lam(y, B, Var(1)))`.

---

## 3. Values (Semantic Domain)

Values are the result of evaluation. They use de Bruijn **levels**
(counting outward from the top of the context) instead of indices.

```
Val ::=
  -- Functions
  | VPi(n : Name, A : Val, cl : Closure)   -- Π type
  | VLam(n : Name, A : Val, cl : Closure)  -- λ abstraction

  -- Pairs
  | VSigma(n : Name, A : Val, cl : Closure) -- Σ type
  | VPair(a : Val, b : Val)                  -- pair value

  -- Natural numbers
  | VNat
  | VZero
  | VSucc(v : Val)

  -- Lists
  | VList(A : Val)
  | VNil(A : Val)
  | VCons(A : Val, h : Val, t : Val)

  -- Unit
  | VUnit
  | VTt

  -- Sum
  | VSum(A : Val, B : Val)
  | VInl(A : Val, B : Val, v : Val)
  | VInr(A : Val, B : Val, v : Val)

  -- Identity
  | VEq(A : Val, a : Val, b : Val)
  | VRefl

  -- Universes
  | VU(i : ℕ)

  -- Axiomatized primitive types
  | VString | VInt | VFloat | VAttrs | VPath | VFunction | VAny

  -- Primitive literal values
  | VStringLit(s) | VIntLit(n) | VFloatLit(f)
  | VAttrsLit | VPathLit | VFnLit | VAnyLit

  -- Neutrals (stuck computations)
  | VNe(level : ℕ, spine : [Elim])

Elim ::=
  | EApp(v : Val)
  | EFst
  | ESnd
  | ENatElim(P : Val, z : Val, s : Val)
  | EListElim(A : Val, P : Val, n : Val, c : Val)
  | ESumElim(A : Val, B : Val, P : Val, l : Val, r : Val)
  | EJ(A : Val, a : Val, P : Val, pr : Val, b : Val)
  | EStrEq(arg : Val)

Closure ::= (env : Env, body : Tm)
Env     ::= [Val]          -- list indexed by de Bruijn index

```

### 3.1 Level/index relationship

De Bruijn levels count from the outermost binder: 0 = first-ever
bound variable. Levels are stable under context extension.

Conversion between index and level:

```
index = depth - level - 1
level = depth - index - 1

```

where `depth` is the current binding depth (length of the context).

### 3.2 Fresh variables

A fresh variable at depth `d` is `VNe(d, [])` — a neutral with
level `d` and empty spine. Used in conversion checking to compare
under binders.

### 3.3 Closure instantiation

```
instantiate((env, body), v) = eval([v] ++ env, body)

```

---

## 4. Evaluation Rules

`eval(ρ, t)` interprets term `t` in environment `ρ`, producing
a value. All rules are deterministic.

### 4.1 Variables and let

```
eval(ρ, Var(i))           = ρ[i]
eval(ρ, Let(n, A, t, u))  = eval([eval(ρ, t)] ++ ρ, u)
eval(ρ, Ann(t, A))        = eval(ρ, t)

```

### 4.2 Functions

```
eval(ρ, Pi(n, A, B))   = VPi(n, eval(ρ, A), (ρ, B))
eval(ρ, Lam(n, A, t))  = VLam(n, eval(ρ, A), (ρ, t))
eval(ρ, App(t, u))     = vApp(eval(ρ, t), eval(ρ, u))

```

where `vApp` performs beta reduction or accumulates:

```
vApp(VLam(n, A, cl), v)  = instantiate(cl, v)
vApp(VNe(l, sp), v)      = VNe(l, sp ++ [EApp(v)])
vApp(_, _)               = THROW "kernel bug: vApp on non-function"

```

### 4.3 Pairs

```
eval(ρ, Sigma(n, A, B))  = VSigma(n, eval(ρ, A), (ρ, B))
eval(ρ, Pair(a, b, T))   = VPair(eval(ρ, a), eval(ρ, b))
eval(ρ, Fst(t))          = vFst(eval(ρ, t))
eval(ρ, Snd(t))          = vSnd(eval(ρ, t))

```

where:

```
vFst(VPair(a, b))   = a
vFst(VNe(l, sp))    = VNe(l, sp ++ [EFst])
vFst(_)             = THROW "kernel bug: vFst on non-pair"

vSnd(VPair(a, b))   = b
vSnd(VNe(l, sp))    = VNe(l, sp ++ [ESnd])
vSnd(_)             = THROW "kernel bug: vSnd on non-pair"

```

### 4.4 Natural numbers

```
eval(ρ, Nat)             = VNat
eval(ρ, Zero)            = VZero
eval(ρ, Succ(t))         = VSucc(eval(ρ, t))   -- MUST trampoline for deep naturals
eval(ρ, NatElim(P,z,s,n)) = vNatElim(eval(ρ,P), eval(ρ,z), eval(ρ,s), eval(ρ,n))

```

where:

```
vNatElim(P, z, s, VZero)     = z
vNatElim(P, z, s, VSucc(n))  = vApp(vApp(s, n), vNatElim(P, z, s, n))
vNatElim(P, z, s, VNe(l,sp)) = VNe(l, sp ++ [ENatElim(P, z, s)])
vNatElim(_, _, _, _)         = THROW "kernel bug: vNatElim on non-nat"

```

**Note**: `vNatElim` on `VSucc` recurses. The implementation MUST
trampoline this to guarantee O(1) stack depth.

### 4.5 Lists

```
eval(ρ, List(A))            = VList(eval(ρ, A))
eval(ρ, Nil(A))             = VNil(eval(ρ, A))
eval(ρ, Cons(A, h, t))      = VCons(eval(ρ, A), eval(ρ, h), eval(ρ, t))  -- MUST trampoline for deep lists
eval(ρ, ListElim(A,P,n,c,l)) =
  vListElim(eval(ρ,A), eval(ρ,P), eval(ρ,n), eval(ρ,c), eval(ρ,l))

```

where:

```
vListElim(A, P, n, c, VNil(_))         = n
vListElim(A, P, n, c, VCons(_, h, t))  =
  vApp(vApp(vApp(c, h), t), vListElim(A, P, n, c, t))
vListElim(A, P, n, c, VNe(l, sp))      =
  VNe(l, sp ++ [EListElim(A, P, n, c)])
vListElim(_, _, _, _, _)               =
  THROW "kernel bug: vListElim on non-list"

```

**Note**: `vListElim` on `VCons` recurses. Must be trampolined.

### 4.6 Unit

```
eval(ρ, Unit)  = VUnit
eval(ρ, Tt)    = VTt

```

Unit has no eliminator in the core. The kernel does NOT implement
eta for Unit — `conv` does not equate arbitrary Unit-typed neutrals
with `VTt`. Two distinct neutrals of type Unit are not definitionally
equal even though they would be in an extensional theory. If eta for
Unit is needed, the elaborator must reduce to `Tt` before submitting
to the kernel.

### 4.7 Sum

```
eval(ρ, Sum(A, B))        = VSum(eval(ρ, A), eval(ρ, B))
eval(ρ, Inl(A, B, t))     = VInl(eval(ρ, A), eval(ρ, B), eval(ρ, t))
eval(ρ, Inr(A, B, t))     = VInr(eval(ρ, A), eval(ρ, B), eval(ρ, t))
eval(ρ, SumElim(A,B,P,l,r,s)) =
  vSumElim(eval(ρ,A), eval(ρ,B), eval(ρ,P), eval(ρ,l), eval(ρ,r), eval(ρ,s))

```

where:

```
vSumElim(A, B, P, l, r, VInl(_, _, v))  = vApp(l, v)
vSumElim(A, B, P, l, r, VInr(_, _, v))  = vApp(r, v)
vSumElim(A, B, P, l, r, VNe(k, sp))     =
  VNe(k, sp ++ [ESumElim(A, B, P, l, r)])
vSumElim(_, _, _, _, _, _)              =
  THROW "kernel bug: vSumElim on non-sum"

```

### 4.8 Identity

```
eval(ρ, Eq(A, a, b))        = VEq(eval(ρ, A), eval(ρ, a), eval(ρ, b))
eval(ρ, Refl)                = VRefl
eval(ρ, J(A, a, P, pr, b, eq)) =
  vJ(eval(ρ,A), eval(ρ,a), eval(ρ,P), eval(ρ,pr), eval(ρ,b), eval(ρ,eq))

```

where:

```
vJ(A, a, P, pr, b, VRefl)    = pr
vJ(A, a, P, pr, b, VNe(l,sp)) =
  VNe(l, sp ++ [EJ(A, a, P, pr, b)])
vJ(_, _, _, _, _, _)          = THROW "kernel bug: vJ on non-refl"

```

### 4.9 Universes

```
eval(ρ, U(i)) = VU(i)

```

### 4.10 Axiomatized primitives

Type formers evaluate to their corresponding values. Literals
carry their payload through. No computation, no recursion — these
are axiomatized constants.

```
eval(ρ, String)       = VString
eval(ρ, Int)          = VInt
eval(ρ, Float)        = VFloat
eval(ρ, Attrs)        = VAttrs
eval(ρ, Path)         = VPath
eval(ρ, Function)     = VFunction
eval(ρ, Any)          = VAny

eval(ρ, StringLit(s)) = VStringLit(s)
eval(ρ, IntLit(n))    = VIntLit(n)
eval(ρ, FloatLit(f))  = VFloatLit(f)
eval(ρ, AttrsLit)     = VAttrsLit
eval(ρ, PathLit)      = VPathLit
eval(ρ, FnLit)        = VFnLit
eval(ρ, AnyLit)       = VAnyLit

```

Most primitives have no eliminators. They exist to integrate
Nix's native types into the kernel's type system as opaque,
axiomatized constants. The exception is String, which has
`StrEq` (§4.11).

### 4.11 String equality (StrEq)

```
eval(ρ, StrEq(lhs, rhs)) = vStrEq(eval(ρ, lhs), eval(ρ, rhs))

```

where:

```
-- trueV / falseV are the plus-encoded derived booleans:
--   trueV  = VDescCon boolDescV VTt (VInl eqTtV eqTtV VRefl)
--   falseV = VDescCon boolDescV VTt (VInr eqTtV eqTtV VRefl)
-- where boolDescV = plus-desc of two VDescRet VTt summands.

vStrEq(VStringLit(s₁), VStringLit(s₂)) = if s₁ == s₂ then trueV else falseV
vStrEq(VNe(l, sp),     rhs)            = VNe(l, sp ++ [EStrEq(rhs)])
vStrEq(lhs,            VNe(l, sp))     = VNe(l, sp ++ [EStrEq(lhs)])
vStrEq(_, _)                           = THROW "kernel bug: vStrEq on non-string"

```

`StrEq` is a binary predicate on strings. Both arguments must be of
type `String`. The result type is the derived `H.bool` —
`μ ⊤ (plus (retI tt) (retI tt)) tt` — which is the kernel
representation of booleans after their retirement as primitives.
Unlike other eliminators, StrEq has no motive: it always returns
`H.bool`, not a dependent type.

When both arguments are concrete string literals, `vStrEq` reduces
to the plus-encoded `true_` or `false_` value by Nix-level string
comparison. When either argument is neutral, the neutral's spine is
extended with `EStrEq` carrying the other argument. This is sound
because `StrEq` is symmetric: `StrEq(a, b) ≡ StrEq(b, a)` for all
`a, b : String`.

---

## 5. Quotation Rules

`quote(d, v)` converts a value back to a term, converting levels to
indices. `d` is the current binding depth.

```
quote(d, VPi(n, A, cl))    = Pi(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VLam(n, A, cl))   = Lam(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VSigma(n, A, cl)) = Sigma(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VPair(a, b))      = Pair(quote(d, a), quote(d, b), _)
quote(d, VNat)             = Nat
quote(d, VZero)            = Zero
quote(d, VSucc(v))         = Succ(quote(d, v))   -- MUST trampoline for deep naturals
quote(d, VList(A))         = List(quote(d, A))
quote(d, VNil(A))          = Nil(quote(d, A))
quote(d, VCons(A, h, t))   = Cons(quote(d, A), quote(d, h), quote(d, t))  -- MUST trampoline for deep lists
quote(d, VUnit)            = Unit
quote(d, VTt)              = Tt
quote(d, VSum(A, B))       = Sum(quote(d, A), quote(d, B))
quote(d, VInl(A, B, v))    = Inl(quote(d, A), quote(d, B), quote(d, v))
quote(d, VInr(A, B, v))    = Inr(quote(d, A), quote(d, B), quote(d, v))
quote(d, VEq(A, a, b))     = Eq(quote(d, A), quote(d, a), quote(d, b))
quote(d, VRefl)            = Refl
quote(d, VU(i))            = U(i)
quote(d, VString)          = String
quote(d, VInt)             = Int
quote(d, VFloat)           = Float
quote(d, VAttrs)           = Attrs
quote(d, VPath)            = Path
quote(d, VFunction)        = Function
quote(d, VAny)             = Any
quote(d, VStringLit(s))    = StringLit(s)
quote(d, VIntLit(n))       = IntLit(n)
quote(d, VFloatLit(f))     = FloatLit(f)
quote(d, VAttrsLit)        = AttrsLit
quote(d, VPathLit)         = PathLit
quote(d, VFnLit)           = FnLit
quote(d, VAnyLit)          = AnyLit
quote(d, VNe(l, sp))       = quoteSp(d, Var(d - l - 1), sp)

quoteSp(d, head, [])                      = head
quoteSp(d, head, [EApp(v) | rest])        = quoteSp(d, App(head, quote(d, v)), rest)
quoteSp(d, head, [EFst | rest])           = quoteSp(d, Fst(head), rest)
quoteSp(d, head, [ESnd | rest])           = quoteSp(d, Snd(head), rest)
quoteSp(d, head, [ENatElim(P,z,s) | rest]) =
  quoteSp(d, NatElim(quote(d,P), quote(d,z), quote(d,s), head), rest)
quoteSp(d, head, [EListElim(A,P,n,c) | rest]) =
  quoteSp(d, ListElim(quote(d,A), quote(d,P), quote(d,n), quote(d,c), head), rest)
quoteSp(d, head, [ESumElim(A,B,P,l,r) | rest]) =
  quoteSp(d, SumElim(quote(d,A), quote(d,B), quote(d,P), quote(d,l), quote(d,r), head), rest)
quoteSp(d, head, [EJ(A,a,P,pr,b) | rest]) =
  quoteSp(d, J(quote(d,A), quote(d,a), quote(d,P), quote(d,pr), quote(d,b), head), rest)
quoteSp(d, head, [EStrEq(arg) | rest]) =
  quoteSp(d, StrEq(head, quote(d, arg)), rest)

fresh(d) = VNe(d, [])

```

---

## 6. Conversion Rules

`conv(d, v₁, v₂)` checks definitional equality of two values at
binding depth `d`. Returns boolean. **No type information is used** —
conversion is purely structural on normalized values.

### 6.1 Structural rules

```
conv(d, VU(i),    VU(j))    = (i == j)
conv(d, VNat,     VNat)     = true
conv(d, VUnit,    VUnit)    = true
conv(d, VZero,    VZero)    = true
conv(d, VTt,      VTt)      = true
conv(d, VRefl,    VRefl)    = true
conv(d, VSucc(a), VSucc(b)) = conv(d, a, b)
conv(d, VString,      VString)      = true
conv(d, VInt,         VInt)         = true
conv(d, VFloat,       VFloat)       = true
conv(d, VAttrs,       VAttrs)       = true
conv(d, VPath,        VPath)        = true
conv(d, VFunction,    VFunction)    = true
conv(d, VAny,         VAny)         = true
conv(d, VStringLit(s₁), VStringLit(s₂)) = (s₁ == s₂)
conv(d, VIntLit(n₁),    VIntLit(n₂))    = (n₁ == n₂)
conv(d, VFloatLit(f₁),  VFloatLit(f₂))  = (f₁ == f₂)
conv(d, VAttrsLit,    VAttrsLit)    = true
conv(d, VPathLit,     VPathLit)     = true
conv(d, VFnLit,       VFnLit)       = true
conv(d, VAnyLit,      VAnyLit)      = true

```

### 6.2 Binding forms

To compare under binders, generate a fresh variable and instantiate:

```
conv(d, VPi(_, A₁, cl₁), VPi(_, A₂, cl₂)) =
  conv(d, A₁, A₂) ∧ conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

conv(d, VLam(_, _, cl₁), VLam(_, _, cl₂)) =
  conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

conv(d, VSigma(_, A₁, cl₁), VSigma(_, A₂, cl₂)) =
  conv(d, A₁, A₂) ∧ conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

```

### 6.3 Compound values

```
conv(d, VPair(a₁, b₁), VPair(a₂, b₂)) =
  conv(d, a₁, a₂) ∧ conv(d, b₁, b₂)

conv(d, VPair(a, b), VNe(l, sp)) =
  conv(d, a, vFst(VNe(l, sp))) ∧ conv(d, b, vSnd(VNe(l, sp)))    -- Σ-η

conv(d, VNe(l, sp), VPair(a, b)) =
  conv(d, vFst(VNe(l, sp)), a) ∧ conv(d, vSnd(VNe(l, sp)), b)    -- Σ-η

conv(d, VTt, VNe(_, _)) = true                                    -- ⊤-η
conv(d, VNe(_, _), VTt) = true                                    -- ⊤-η

conv(d, VList(A₁),        VList(A₂))        = conv(d, A₁, A₂)
conv(d, VNil(A₁),         VNil(A₂))         = conv(d, A₁, A₂)
conv(d, VCons(A₁, h₁, t₁), VCons(A₂, h₂, t₂)) =
  conv(d, A₁, A₂) ∧ conv(d, h₁, h₂) ∧ conv(d, t₁, t₂)

conv(d, VSum(A₁, B₁),           VSum(A₂, B₂))           = conv(d, A₁, A₂) ∧ conv(d, B₁, B₂)
conv(d, VInl(A₁, B₁, v₁),      VInl(A₂, B₂, v₂))      = conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, v₁, v₂)
conv(d, VInr(A₁, B₁, v₁),      VInr(A₂, B₂, v₂))      = conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, v₁, v₂)

conv(d, VEq(A₁, a₁, b₁), VEq(A₂, a₂, b₂)) =
  conv(d, A₁, A₂) ∧ conv(d, a₁, a₂) ∧ conv(d, b₁, b₂)

```

### 6.4 Neutrals

```
conv(d, VNe(l₁, sp₁), VNe(l₂, sp₂)) =
  (l₁ == l₂) ∧ convSp(d, sp₁, sp₂)

convSp(d, [], [])         = true
convSp(d, [e₁|r₁], [e₂|r₂]) = convElim(d, e₁, e₂) ∧ convSp(d, r₁, r₂)
convSp(d, _, _)           = false    -- different lengths

convElim(d, EApp(v₁),   EApp(v₂))   = conv(d, v₁, v₂)
convElim(d, EFst,        EFst)        = true
convElim(d, ESnd,        ESnd)        = true
convElim(d, ENatElim(P₁,z₁,s₁), ENatElim(P₂,z₂,s₂)) =
  conv(d, P₁, P₂) ∧ conv(d, z₁, z₂) ∧ conv(d, s₁, s₂)
convElim(d, EListElim(A₁,P₁,n₁,c₁), EListElim(A₂,P₂,n₂,c₂)) =
  conv(d, A₁, A₂) ∧ conv(d, P₁, P₂) ∧ conv(d, n₁, n₂) ∧ conv(d, c₁, c₂)
convElim(d, ESumElim(A₁,B₁,P₁,l₁,r₁), ESumElim(A₂,B₂,P₂,l₂,r₂)) =
  conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, P₁, P₂) ∧ conv(d, l₁, l₂) ∧ conv(d, r₁, r₂)
convElim(d, EJ(A₁,a₁,P₁,pr₁,b₁), EJ(A₂,a₂,P₂,pr₂,b₂)) =
  conv(d, A₁, A₂) ∧ conv(d, a₁, a₂) ∧ conv(d, P₁, P₂) ∧ conv(d, pr₁, pr₂) ∧ conv(d, b₁, b₂)
convElim(d, EStrEq(arg₁), EStrEq(arg₂)) = conv(d, arg₁, arg₂)
convElim(_, _, _) = false

```

### 6.5 Catch-all

```
conv(d, _, _) = false

```

Any pair of values not matching the above rules is not definitionally
equal. **No Pi-eta**: `f` and `λx. f x` are NOT equated; if the
elaborator needs them equal, it must eta-expand `f` before submitting
to the kernel. **Σ-eta and ⊤-eta are applied** (see §6.3): a pair
`⟨a, b⟩` converts against a neutral `x : Σ` by projecting both sides,
and any neutral of type `⊤` converts against `tt`. Σ-eta and ⊤-eta are
sound in the type-free conv because conv is always called on two values
sharing a type — the neutral's shape (Σ or ⊤) is witnessed by the
non-neutral side.

---

## 7. Typing Rules (Bidirectional)

### 7.1 Contexts

```
Ctx ::= {
  env   : Env,           -- values for evaluation
  types : [Val],         -- types of bound variables (indexed by de Bruijn)
  depth : ℕ              -- current binding depth
}

emptyCtx = { env = [], types = [], depth = 0 }

extend(Γ, n, A) = {
  env   = [fresh(Γ.depth)] ++ Γ.env,
  types = [A] ++ Γ.types,
  depth = Γ.depth + 1
}

lookupType(Γ, i) = Γ.types[i]
  -- THROW if i >= length(Γ.types)

```

### 7.2 Notation

```
Γ ⊢ t ⇐ A  ↝  t'     checking mode:  check(Γ, t, A) = t'
Γ ⊢ t ⇒ A  ↝  t'     synthesis mode: infer(Γ, t) = (t', A)
Γ ⊢ T type  ↝  T'     type formation: checkType(Γ, T) = T'
Γ ⊢ T type@i  ↝  T'   type + level:  checkTypeLevel(Γ, T) = (T', i)

```

The output `t'` is the elaborated core term (fully annotated).

### 7.3 Synthesis rules (infer)

**Var**

```
                lookupType(Γ, i) = A
                ──────────────────────
                Γ ⊢ Var(i) ⇒ A  ↝  Var(i)

```

**Ann** (annotation)

```
                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ ⊢ t ⇐ Â  ↝  t'
                ──────────────────────
                Γ ⊢ Ann(t, A) ⇒ Â  ↝  Ann(t', A')

```

**App** (application)

```
                Γ ⊢ f ⇒ fTy  ↝  f'
                whnf(fTy) = VPi(n, A, cl)
                Γ ⊢ u ⇐ A  ↝  u'
                B = instantiate(cl, eval(Γ.env, u'))
                ──────────────────────
                Γ ⊢ App(f, u) ⇒ B  ↝  App(f', u')

```

**CRITICAL**: `whnf(fTy)` must normalize `fTy` to weak head normal
form before pattern matching. If `fTy` is a let-unfolding or a
neutral that reduces further, the match will fail spuriously.

In this kernel, `eval` already produces WHNF, so `whnf(v) = v` for
all values. But this invariant must be maintained if the value
representation changes.

**Fst** (first projection)

```
                Γ ⊢ t ⇒ tTy  ↝  t'
                whnf(tTy) = VSigma(n, A, cl)
                ──────────────────────
                Γ ⊢ Fst(t) ⇒ A  ↝  Fst(t')

```

**Snd** (second projection)

```
                Γ ⊢ t ⇒ tTy  ↝  t'
                whnf(tTy) = VSigma(n, A, cl)
                B = instantiate(cl, vFst(eval(Γ.env, t')))
                ──────────────────────
                Γ ⊢ Snd(t) ⇒ B  ↝  Snd(t')

```

**Eliminator motive checking (checkMotive).**
All eliminators require a motive `P : domTy → U(k)` for some `k`.
The implementation provides a shared `checkMotive` helper that
handles two forms:

- Lambda motives (`P = λx. body`): extend the context with `x : domTy`
  and verify `body` is a type via `checkType`.
- Non-lambda motives: infer the type and verify it has shape
  `VPi(_, domTy, _ → VU(k))` for some `k`.

The `k` is not fixed — motives may target any universe level,
enabling **large elimination** (eliminators whose return type is a
type, not a value). For example, `NatElim(λn. U(0), ...)` is valid
and returns types at universe 1.

**NatElim**

```
                Γ ⊢ P ⇐ VPi(_, VNat, ([], U(k)))  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ z ⇐ vApp(P̂, VZero)  ↝  z'
                Γ ⊢ s ⇐ VPi(_, VNat, (Γ.env, Pi(_, App(P, Var(0)), ...)))  ↝  s'
                   -- s : Π(k : ℕ). P(k) → P(S(k))
                Γ ⊢ n ⇐ VNat  ↝  n'
                ──────────────────────
                Γ ⊢ NatElim(P, z, s, n) ⇒ vApp(P̂, eval(Γ.env, n'))
                   ↝  NatElim(P', z', s', n')

```

The full typing of `s` is:

```
s : Π(k : ℕ). P(k) → P(S(k))

```
This is checked by constructing the appropriate Pi type from `P̂`.

**ListElim**

```
                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ ⊢ P ⇐ VPi(_, VList(Â), ([], U(k)))  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ n ⇐ vApp(P̂, VNil(Â))  ↝  n'
                Γ ⊢ c ⇐ <Π(h:A). Π(t:List A). P(t) → P(cons h t)>  ↝  c'
                Γ ⊢ l ⇐ VList(Â)  ↝  l'
                ──────────────────────
                Γ ⊢ ListElim(A, P, n, c, l) ⇒ vApp(P̂, eval(Γ.env, l'))
                   ↝  ListElim(A', P', n', c', l')

```

**SumElim**

```
                Γ ⊢ A type  ↝  A'    Â = eval(Γ.env, A')
                Γ ⊢ B type  ↝  B'    B̂ = eval(Γ.env, B')
                Γ ⊢ P ⇐ VPi(_, VSum(Â, B̂), ([], U(k)))  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ l ⇐ VPi(_, Â, <P(inl x)>)  ↝  l'
                Γ ⊢ r ⇐ VPi(_, B̂, <P(inr y)>)  ↝  r'
                Γ ⊢ s ⇐ VSum(Â, B̂)  ↝  s'
                ──────────────────────
                Γ ⊢ SumElim(A,B,P,l,r,s) ⇒ vApp(P̂, eval(Γ.env, s'))
                   ↝  SumElim(A',B',P',l',r',s')

```

**J** (identity elimination)

```
                Γ ⊢ A type  ↝  A'    Â = eval(Γ.env, A')
                Γ ⊢ a ⇐ Â  ↝  a'    â = eval(Γ.env, a')
                Γ ⊢ P ⇐ <Π(y : A). Π(e : Id_A(a, y)). U(k)>  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ pr ⇐ vApp(vApp(P̂, â), VRefl)  ↝  pr'
                Γ ⊢ b ⇐ Â  ↝  b'    b̂ = eval(Γ.env, b')
                Γ ⊢ eq ⇐ VEq(Â, â, b̂)  ↝  eq'
                ──────────────────────
                Γ ⊢ J(A, a, P, pr, b, eq) ⇒ vApp(vApp(P̂, b̂), eval(Γ.env, eq'))
                   ↝  J(A', a', P', pr', b', eq')

```

**J motive verification.** For non-lambda motives, the
implementation structurally verifies all three components:

1. Outer Pi domain matches `A` (conversion check)
2. Inner Pi domain matches `Eq(A, a, y)` (conversion check)
3. Innermost codomain is `VU(k)` for some `k`

For lambda motives (`P = λy. body`), the body is checked via
`checkMotive` against `Eq(A, a, y)`, which performs the same
verification on the inner structure. This catches motive errors
at the motive itself rather than deferring to the base case.

**Axiomatized primitive type formers** (synthesis)

Primitive type formers are synthesized directly — they infer as
inhabitants of `U(0)`:

```
                ──────────────────────
                Γ ⊢ String ⇒ VU(0)  ↝  String

                ──────────────────────
                Γ ⊢ Int ⇒ VU(0)  ↝  Int

```

(Similarly for Float, Attrs, Path, Function, Any — all at level 0.)

**Primitive literals** (synthesis)

Literals synthesize their corresponding type:

```
                ──────────────────────
                Γ ⊢ StringLit(s) ⇒ VString  ↝  StringLit(s)

                ──────────────────────
                Γ ⊢ IntLit(n) ⇒ VInt  ↝  IntLit(n)

                ──────────────────────
                Γ ⊢ FloatLit(f) ⇒ VFloat  ↝  FloatLit(f)

```

(Similarly for AttrsLit → VAttrs, PathLit → VPath,
FnLit → VFunction, AnyLit → VAny.)

**StrEq** (string equality)

```
                boolV = VMu VUnit (VDescPlus (VDescRet VTt) (VDescRet VTt)) VTt
                Γ ⊢ lhs ⇐ VString  ↝  lhs'
                Γ ⊢ rhs ⇐ VString  ↝  rhs'
                ──────────────────────
                Γ ⊢ StrEq(lhs, rhs) ⇒ boolV  ↝  StrEq(lhs', rhs')

```

Both arguments are checked against `VString`. The result type is
the derived `H.bool` — `μ ⊤ (plus (retI tt) (retI tt)) tt` —
written `boolV` above. StrEq is not a dependent eliminator: it has
no motive parameter.

### 7.4 Checking rules (check)

**Lam** (lambda introduction)

```
                whnf(A) = VPi(n, dom, cl)
                Γ' = extend(Γ, n, dom)
                cod = instantiate(cl, fresh(Γ.depth))
                Γ' ⊢ t ⇐ cod  ↝  t'
                ──────────────────────
                Γ ⊢ Lam(n, _, t) ⇐ A  ↝  Lam(n, quote(Γ.depth, dom), t')

```

**Pair** (pair introduction)

```
                whnf(T) = VSigma(n, A, cl)
                Γ ⊢ a ⇐ A  ↝  a'
                B = instantiate(cl, eval(Γ.env, a'))
                Γ ⊢ b ⇐ B  ↝  b'
                ──────────────────────
                Γ ⊢ Pair(a, b, _) ⇐ T  ↝  Pair(a', b', quote(Γ.depth, T))

```

**Zero**

```
                whnf(A) = VNat
                ──────────────────────
                Γ ⊢ Zero ⇐ A  ↝  Zero

```

**Succ** (MUST trampoline for deep naturals)

```
                whnf(A) = VNat
                Γ ⊢ t ⇐ VNat  ↝  t'
                ──────────────────────
                Γ ⊢ Succ(t) ⇐ A  ↝  Succ(t')

```

**Nil**

```
                whnf(A) = VList(Â)
                ──────────────────────
                Γ ⊢ Nil(_) ⇐ A  ↝  Nil(quote(Γ.depth, Â))

```

**Cons** (MUST trampoline for deep lists)

```
                whnf(A) = VList(Â)
                Γ ⊢ h ⇐ Â  ↝  h'
                Γ ⊢ t ⇐ VList(Â)  ↝  t'
                ──────────────────────
                Γ ⊢ Cons(_, h, t) ⇐ A  ↝  Cons(quote(Γ.depth, Â), h', t')

```

**Tt**

```
                whnf(A) = VUnit
                ──────────────────────
                Γ ⊢ Tt ⇐ A  ↝  Tt

```

**Inl / Inr**

```
                whnf(T) = VSum(A, B)
                Γ ⊢ t ⇐ A  ↝  t'
                ──────────────────────
                Γ ⊢ Inl(_, _, t) ⇐ T  ↝  Inl(quote(Γ.depth, A), quote(Γ.depth, B), t')

                whnf(T) = VSum(A, B)
                Γ ⊢ t ⇐ B  ↝  t'
                ──────────────────────
                Γ ⊢ Inr(_, _, t) ⇐ T  ↝  Inr(quote(Γ.depth, A), quote(Γ.depth, B), t')

```

**Refl**

```
                whnf(T) = VEq(A, a, b)
                conv(Γ.depth, a, b) = true
                ──────────────────────
                Γ ⊢ Refl ⇐ T  ↝  Refl

```

If `conv(Γ.depth, a, b) = false`, this is a **type error**: the
two sides of the equation are not definitionally equal, and `refl`
cannot prove the equation. Report via effect.

**Primitive literals** (checked against their corresponding types)

```
                whnf(A) = VString
                ──────────────────────
                Γ ⊢ StringLit(s) ⇐ A  ↝  StringLit(s)

                whnf(A) = VInt
                ──────────────────────
                Γ ⊢ IntLit(n) ⇐ A  ↝  IntLit(n)

                whnf(A) = VFloat
                ──────────────────────
                Γ ⊢ FloatLit(f) ⇐ A  ↝  FloatLit(f)

                whnf(A) = VAttrs
                ──────────────────────
                Γ ⊢ AttrsLit ⇐ A  ↝  AttrsLit

                whnf(A) = VPath
                ──────────────────────
                Γ ⊢ PathLit ⇐ A  ↝  PathLit

                whnf(A) = VFunction
                ──────────────────────
                Γ ⊢ FnLit ⇐ A  ↝  FnLit

                whnf(A) = VAny
                ──────────────────────
                Γ ⊢ AnyLit ⇐ A  ↝  AnyLit

```

**Let**

```
                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ ⊢ t ⇐ Â  ↝  t'
                t̂ = eval(Γ.env, t')
                Γ' = { env = [t̂] ++ Γ.env, types = [Â] ++ Γ.types, depth = Γ.depth + 1 }
                Γ' ⊢ u ⇐ B  ↝  u'
                ──────────────────────
                Γ ⊢ Let(n, A, t, u) ⇐ B  ↝  Let(n, A', t', u')

```

Note: `Let` in checking mode — the expected type `B` is for the
body `u`, not for the definition `t`.

**Sub** (mode switch: fall through to synthesis)

```
                Γ ⊢ t ⇒ A  ↝  t'
                conv(Γ.depth, A, B) = true   -- or cumulativity check
                ──────────────────────
                Γ ⊢ t ⇐ B  ↝  t'

```

This is the catch-all. If no other checking rule applies, try
synthesis and verify the inferred type matches the expected type.

### 7.5 Type formation (checkType / checkTypeLevel)

The implementation provides two variants: `checkType(Γ, T)` returns
only the elaborated term, while `checkTypeLevel(Γ, T)` returns both
the elaborated term and the universe level. `checkType` is a thin
wrapper: `checkType(Γ, T) = checkTypeLevel(Γ, T).term`. Universe
levels are computed structurally during the type formation check
(see §8.2), not by post-hoc inspection of evaluated values.

```
                ──────────────────────
                Γ ⊢ Nat type  ↝  Nat

                ──────────────────────
                Γ ⊢ Unit type  ↝  Unit

                ──────────────────────
                Γ ⊢ String type  ↝  String

                (Similarly for Int, Float, Attrs, Path, Function, Any)

                ──────────────────────
                Γ ⊢ U(i) type  ↝  U(i)

                Γ ⊢ A type  ↝  A'
                ──────────────────────
                Γ ⊢ List(A) type  ↝  List(A')

                Γ ⊢ A type  ↝  A'       Γ ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ Sum(A, B) type  ↝  Sum(A', B')

                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ' = extend(Γ, n, Â)
                Γ' ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ Pi(n, A, B) type  ↝  Pi(n, A', B')

                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ' = extend(Γ, n, Â)
                Γ' ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ Sigma(n, A, B) type  ↝  Sigma(n, A', B')

                Γ ⊢ A type  ↝  A'     Â = eval(Γ.env, A')
                Γ ⊢ a ⇐ Â  ↝  a'
                Γ ⊢ b ⇐ Â  ↝  b'
                ──────────────────────
                Γ ⊢ Eq(A, a, b) type  ↝  Eq(A', a', b')

                -- Fallback: infer and check it's a universe
                Γ ⊢ T ⇒ A  ↝  T'
                whnf(A) = VU(i)
                ──────────────────────
                Γ ⊢ T type  ↝  T'

```

---

## 8. Universe Rules

### 8.1 Universe formation

```
U(i) : U(i + 1)                for all i ≥ 0

```

### 8.2 Type former levels

Universe levels are computed by `checkTypeLevel`, which returns
`{ term; level; }` from the **typing derivation**, not from
post-hoc value inspection. This avoids the problem of unknown
levels for neutral type variables. We write `level(A)` as shorthand
for `checkTypeLevel(Γ, A).level`.

```
checkTypeLevel(Γ, Nat)         = { Nat,     0 }
checkTypeLevel(Γ, Unit)        = { Unit,    0 }
checkTypeLevel(Γ, String)      = { String,  0 }
checkTypeLevel(Γ, Int)         = { Int,     0 }
checkTypeLevel(Γ, Float)       = { Float,   0 }
checkTypeLevel(Γ, Attrs)       = { Attrs,   0 }
checkTypeLevel(Γ, Path)        = { Path,    0 }
checkTypeLevel(Γ, Function)    = { Function, 0 }
checkTypeLevel(Γ, Any)         = { Any,     0 }
checkTypeLevel(Γ, List(A))     = { List(A'), level(A) }
checkTypeLevel(Γ, Sum(A, B))   = { Sum(A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, Pi(n, A, B)) = { Pi(n,A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, Sigma(n,A,B))= { Sigma(n,A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, Eq(A, a, b)) = { Eq(A',a',b'), level(A) }
checkTypeLevel(Γ, U(i))        = { U(i),   i + 1 }
-- Fallback: infer type, require VU(i), extract i
checkTypeLevel(Γ, T)           = { T', i }  where Γ ⊢ T ⇒ VU(i)

```

The fallback handles neutral type expressions (variables,
applications) by inferring their type and requiring it to be a
universe. This correctly propagates levels through type variables:
if `B : U(1)`, then `checkTypeLevel` on `B` infers `VU(1)` and
returns level 1.

### 8.3 Cumulativity

A type `A` at level `i` is also a type at level `j` for all `j > i`.
This is implemented by accepting `conv(d, VU(i), VU(j))` when `i ≤ j`
**in the Sub rule only** (checking mode, when comparing an inferred
universe against an expected universe). The `conv` function itself
uses strict equality `i == j`.

The cumulativity check is in `check`:

```
-- In the Sub rule:
-- If inferredTy = VU(i) and expectedTy = VU(j) and i ≤ j:  accept
-- Otherwise: conv(Γ.depth, inferredTy, expectedTy) must hold

```

### 8.4 Universe consistency

The kernel MUST reject `U(i) : U(i)`. This is guaranteed by the
level computation: `level(U(i)) = i + 1`, so `U(i)` lives at level
`i + 1`, not `i`. Self-containing universes cannot be constructed.

This prevents Girard's paradox (Girard 1972), which requires a type
that contains itself. Hurkens (1995) gives the compact MLTT rendering
of the inconsistency proof. Universe stratification is the standard
fix, and it is why the kernel enforces `level(U(i)) = i + 1`.

---

## 9. Fuel Mechanism

### 9.1 Evaluation fuel

Every call to `evalF` receives a fuel parameter and decrements it
by one before evaluating the term. When fuel reaches 0:

```
evalF(fuel=0, ρ, t) = THROW "normalization budget exceeded"

```

The kernel aborts via `throw`. Layer 0 (TCB) has no access to the
effect system by design, so fuel exhaustion and kernel invariant
violations both manifest as Nix-level throws caught by `tryEval`.
Callers should treat any throw from the evaluator as "term not
verified" — the distinction between fuel exhaustion and a kernel bug
is in the error message text, not the failure mechanism.

### 9.2 Default budget

The default fuel budget is 10,000,000 reduction steps. This is
configurable by the caller via `evalF`. No minimum is enforced —
callers may pass arbitrarily low fuel, which will cause immediate
`throw` on the first eval step.

### 9.3 Fuel accounting

Fuel is **per-path**, not a global counter. Each call to `evalF`
captures `f = fuel - 1` and passes `f` to all sub-evaluations of
that term. When evaluating `App(t, u)`, both `evalF(f, ρ, t)` and
`evalF(f, ρ, u)` receive the same `f`. This means fuel bounds the
**depth** of any single evaluation path, not the total work across
all paths.

For a balanced binary tree of N applications, the total work is
O(2^depth × fuel), not O(fuel). This is inherent to pure Nix —
there is no mutable global counter. The fuel mechanism guarantees
termination (every path eventually hits 0) but does not bound total
computation time.

All fuel consumption flows through `evalF`:

- Direct term evaluation (each `evalF` call decrements fuel by 1)
- Beta-reduction in `vApp` consumes fuel indirectly via
  `instantiateF`, which calls `evalF`
- Iota-reduction in recursive eliminators (`vNatElimF`,
  `vListElimF`, `vSumElimF`) consumes fuel indirectly via `vAppF`

Non-recursive eliminators (`vJ`) complete in O(1) and do not call
`evalF`. Structural operations (building values, pattern matching
on tags) do not consume fuel.

### 9.4 Fuel threading in trampolined eliminators

Trampolined eliminators (`vNatElimF`, `vListElimF`) flatten
recursive chains into `builtins.foldl'` loops. Each fold step
threads fuel through the accumulator:

```
foldl'(λ{acc, fuel}. λi.
  if fuel ≤ 0 then THROW "normalization budget exceeded"
  else { acc = step(fuel, acc, chain[i]); fuel = fuel - 1; })
  {acc = base; fuel = fuel}
  [1..n]

```

This ensures that an N-element chain consumes N units of fuel from
the fold, plus whatever fuel each step application consumes
internally. Without this threading, each step would get the
original fuel budget, giving an effective budget of N × fuel.

The worst-case complexity of a threaded fold is O(fuel²): at step
*i*, the inner `vAppF` receives `fuel - i` as its own per-path
budget. Summing over all steps gives Σ(fuel - i) ≈ fuel²/2. To
achieve O(fuel), `vAppF` would need to return remaining fuel — an
invasive signature change. The quadratic residual is inherent to
per-path fuel semantics and is a strict improvement over the
pre-threading O(N × fuel) with unbounded N.

### 9.5 Fuel consumption in constructor chains

Trampolined Succ and Cons evaluation (`eval(ρ, Succ(t))` and
`eval(ρ, Cons(A, h, t))`) flatten chains of n constructors and
deduct n fuel units from the budget before evaluating the base.
A chain of n Succ constructors consumes n+1 fuel (1 for the entry
evaluation, n for the chain deduction). Cons chains additionally
thread remaining fuel through the fold: each fold step evaluates
the element type and head with the current fuel budget, then
decrements by 1 (matching the eliminator fuel threading pattern
from §9.4). This is a third fuel consumption site alongside
`evalF` decrements and eliminator fold steps.

---

## 10. Properties the Implementation Must Satisfy

### 10.1 Soundness (non-negotiable)

If the kernel accepts `Γ ⊢ t : A`, then `t` is a valid term of
type `A` in MLTT with the specified type formers and universe
hierarchy. Formally:

**If `check(Γ, t, A)` succeeds, then `Γ ⊢ t : A` is derivable
in the declarative typing rules of MLTT.**

Equivalently: the kernel never accepts an ill-typed term.

### 10.2 Determinism

For any input `(Γ, t, A)`, the kernel produces the same result
on every invocation. There is no randomness, no system-dependent
behavior, no sensitivity to evaluation order (beyond fuel
exhaustion, which always rejects).

### 10.3 Termination

For any input `(Γ, t, A)`, the kernel terminates. It either:
- Accepts (returns the elaborated term)
- Rejects with a type error (via effect)
- Rejects with fuel exhaustion
- Crashes with a kernel bug diagnostic (throw)

It never loops. The fuel mechanism guarantees this.

### 10.4 Evaluation roundtrip

For any well-typed term `t` and environment `ρ` consistent with
the context:

```
quote(d, eval(ρ, quote(d, eval(ρ, t)))) = quote(d, eval(ρ, t))

```

Evaluation followed by quotation is idempotent. The result is a
normal form.

### 10.5 Conversion reflexivity

For any value `v`:

```
conv(d, v, v) = true

```

### 10.6 Conversion symmetry

For any values `v₁, v₂`:

```
conv(d, v₁, v₂) = conv(d, v₂, v₁)

```

### 10.7 Conversion transitivity

For any values `v₁, v₂, v₃`:

```
conv(d, v₁, v₂) ∧ conv(d, v₂, v₃)  ⟹  conv(d, v₁, v₃)

```

### 10.8 Type preservation under evaluation

If `Γ ⊢ t : A` and `eval(Γ.env, t) = v`, then `v` represents a
value of type `A`. This is not directly testable (values don't
carry types) but is ensured by the correctness of the evaluation
rules.

### 10.9 Strong normalization (for well-typed terms)

For any well-typed term `t`, `eval` terminates without exhausting
fuel for a sufficiently large fuel budget. The fuel mechanism is
a practical safeguard, not a theoretical necessity for well-typed
terms.

---

## 11. Derived Test Cases

Every rule in this spec generates at least one positive test (the
rule applies and succeeds) and one negative test (the rule's
premises are violated and the kernel rejects).

### 11.1 Required positive tests (kernel must ACCEPT)

```
-- Identity
⊢ Refl : Eq(Nat, Zero, Zero)

-- Function type
⊢ Lam(x, Nat, Var(0)) : Pi(x, Nat, Nat)

-- Application
f : Pi(x, Nat, Nat) ⊢ App(f, Zero) : Nat

-- Dependent function
⊢ Lam(A, U(0), Lam(x, Var(0), Var(0))) : Pi(A, U(0), Pi(x, A, A))

-- Sigma pair
⊢ Pair(Zero, Tt, Sigma(x, Nat, Unit)) : Sigma(x, Nat, Unit)

-- Nat induction: 0 + 0 = 0
⊢ Refl : Eq(Nat, NatElim(_, Zero, _, Zero), Zero)

-- List
⊢ Cons(Nat, Zero, Nil(Nat)) : List(Nat)

-- Sum injection
⊢ Inl(Nat, Unit, Zero) : Sum(Nat, Unit)

-- Universe hierarchy
⊢ U(0) : U(1)
⊢ U(1) : U(2)
⊢ Nat : U(0)
⊢ Pi(x, Nat, Nat) : U(0)

-- Let binding
⊢ Let(x, Nat, Zero, Var(0)) : Nat

-- Cumulativity: Nat : U(0) should also be accepted at U(1)

-- StrEq: type inference returns the derived H.bool
--   (= μ ⊤ (plus (retI tt) (retI tt)) tt; see §4.11)
⊢ StrEq(StringLit("a"), StringLit("b")) : H.bool

-- StrEq reduction: equal strings reduce to the derived true_ value;
-- unequal strings reduce to false_. Both witnessed via Refl over the
-- derived-bool form. Expressing this rule at the Tm level requires
-- the plus/μ machinery; see the examples/verified-functions.nix
-- fixture `recordStrEqMatch` for an executable test.

```

### 11.2 Required negative tests (kernel must REJECT)

```
-- Type mismatch
⊢ Zero : Unit                          REJECT

-- Universe violation
⊢ U(0) : U(0)                          REJECT

-- Refl on unequal terms
⊢ Refl : Eq(Nat, Zero, Succ(Zero))     REJECT

-- Application of non-function
⊢ App(Zero, Zero)                      REJECT

-- Projection of non-pair
⊢ Fst(Zero)                            REJECT

-- Wrong eliminator scrutinee
⊢ NatElim(_, _, _, Tt)                 REJECT  (Tt : Unit, not Nat)

-- Unbound variable
⊢ Var(0)  (in empty context)           REJECT

-- StrEq on non-string
⊢ StrEq(Zero, StringLit("foo"))       REJECT  (lhs is Nat, expected String)

-- Ill-typed pair
⊢ Pair(Zero, Zero, Sigma(x, Nat, Unit))  REJECT  (snd is Nat, expected Unit)

```

### 11.3 Required stress tests

```
-- Large Nat: S^5000(0) : Nat                     ACCEPT (trampoline)
-- Large List: cons^5000 : List(Nat)              ACCEPT (trampoline)
-- NatElim on S^5000(0)                            ACCEPT (trampoline)
-- ListElim on cons^5000                           ACCEPT (trampoline)
-- Succ elaboration: elab-succ-5000               ACCEPT (trampoline)
-- Cons elaboration: elab-cons-5000               ACCEPT (trampoline)
-- Deeply nested Pi: Pi(x₁, ..., Pi(xₙ, Nat, Nat)...) for n=500  ACCEPT
-- Fuel exhaustion: artificially low fuel on complex term    REJECT (fuel)
-- Fuel threading: NatElim fold decrements fuel per step    ACCEPT
-- Fuel threading: ListElim fold decrements fuel per step   ACCEPT

```

### 11.4 Required roundtrip tests

For each value form, verify:

```
quote(d, eval(ρ, t)) = normal_form(t)

```

where `normal_form(t)` is the expected normal form.

---

## 12. Notation Index

| Symbol | Meaning |
|--------|---------|
| Γ | Typing context |
| ρ | Value environment |
| d | Binding depth (for levels ↔ indices) |
| ⊢ | Typing judgment |
| ⇐ | Checking mode |
| ⇒ | Synthesis mode |
| ↝ | Elaborates to |
| ≡ | Definitional equality |
| Π | Dependent function type |
| Σ | Dependent pair type |
| ℕ | Natural numbers |
| 𝔹 | Booleans (derived: `μ ⊤ (plus (retI tt) (retI tt)) tt`) |
| ⊤ | Unit type |
| ⊥ | Void / empty type (derived: `Fin 0`) |
| U(i) | Universe at level i |
| Id_A(a,b) | Identity type |
| TCB | Trusted computing base |
| WHNF | Weak head normal form |
| NbE | Normalization by evaluation |
| THROW | Kernel invariant violation (crash) |
| REJECT | Term rejected (via effect or fuel) |

---

## 13. Known Limitations

The following are documented implementation choices or limitations,
not bugs. They are recorded here so auditors do not rediscover them.

### 13.1 Pair quotation uses dummy type annotation

`quote(d, VPair(a, b))` produces `Pair(quote(d,a), quote(d,b), Unit)`
— the type annotation is always `Unit` regardless of the actual pair
type. The `VPair` value does not carry its type (values are untyped
in NbE), so the annotation cannot be reconstructed without additional
context. Quoted pairs are structurally correct but carry a dummy
annotation.

### 13.2 Lambda domain annotations discarded in checking mode

When checking `Lam(n, A, t)` against `VPi(n, dom, cl)`, the lambda's
domain annotation `A` is discarded and replaced by `dom` from the
Pi type. This is standard bidirectional type checking (Dunfield &
Krishnaswami 2021, §4): in checking mode, the expected type provides
the domain, not the term. The elaborated output uses `quote(d, dom)`,
making the original annotation unrecoverable.

### 13.3 Term constructors do not validate argument types

Term constructors (`mkVar`, `mkSucc`, etc.) accept arbitrary Nix
values without type validation. `mkVar "hello"` produces
`{ tag = "var"; idx = "hello"; }`, which crashes at eval time.
The trust boundary is the HOAS layer (`hoas.nix`), which is the
public API — direct term construction is internal to the kernel.

### 13.4 `tryEval` only catches `throw` and `assert false`

`builtins.tryEval` in the elaborator's `isConstantFamily` sentinel
detection only catches explicit `throw` and `assert false`. Nix
coercion errors (e.g., "cannot convert a function to JSON"),
missing attribute access, and type comparison errors are uncatchable.
The elaborator uses `builtins.typeOf` in error paths to avoid
triggering coercion errors.

### 13.5 HOAS sentinel comparison

The `isConstantFamily` sentinel test in the elaborator applies two
distinct sentinel values and compares the results to detect whether
a binding body is dependent. Both Pi and Sigma paths compare
**elaborated kernel terms** (`H.elab r1.value == H.elab r2.value`)
rather than raw HOAS trees. This avoids false negatives from Nix's
function identity comparison (`==` on lambdas). However, if `H.elab`
itself produces structurally different terms for semantically
equivalent types (e.g., through different elaboration paths), false
negatives remain possible. This is a safe failure mode — the kernel
still type-checks correctly, but elaboration may require explicit
`_kernel` annotations unnecessarily.

### 13.6 StrEq neutral canonicalization

When one argument to `vStrEq` is neutral and the other is a literal,
the neutral's spine is extended with `EStrEq(literal)`. When both
arguments are neutral, the **left** neutral's spine is extended with
`EStrEq(right)`. This means `StrEq(x, y)` and `StrEq(y, x)` (where
both are neutral) produce different normal forms: `VNe(x, [EStrEq(y)])`
vs `VNe(y, [EStrEq(x)])`. Therefore `conv` will report them as
**not** definitionally equal, even though `StrEq` is semantically
symmetric. This is a safe conservatism: the kernel may reject some
provable equalities but never accepts a false one.

### 13.7 Extract uses type value threading (not sentinels)

The `extract` function threads kernel type values (`tyVal`) through
recursive extraction, rather than using sentinel-based non-dependence
tests. For Pi extraction, the codomain type is computed per-invocation
via `instantiate(tyVal.closure, kernelArg)`, supporting both dependent
and non-dependent function extraction. For Sigma extraction (records),
the second component's type is computed via
`instantiate(tyVal.closure, val.fst)`. A `reifyType : Val → HoasTree`
fallback converts kernel type values back to HOAS when the HOAS body
cannot be applied (e.g., when the body accesses record fields from a
neutral). `reifyType` loses sugar (VSigma → `H.sigma`, not
`H.record`) so the HOAS body is preferred when available.

### 13.8 Spine comparison complexity

`convSp` uses `builtins.elemAt` in a fold to compare neutral spines.
In Nix, `builtins.elemAt` on lists is O(1) (Nix lists are internally
vectors/arrays), so the actual complexity is O(n), not O(n²). This
was incorrectly flagged in an earlier audit.

---

## References

1. Coquand, T. et al. (2009). *A simple type-theoretic language: Mini-TT.*
2. Dunfield, J. & Krishnaswami, N. (2021). *Bidirectional Typing.* ACM Computing Surveys.
3. Kovács, A. (2022). *Generalized Universe Hierarchies.* CSL 2022.
4. Abel, A. & Chapman, J. (2014). *Normalization by Evaluation in the Delay Monad.*
5. Girard, J.-Y. (1972). *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur.* Thèse d'État, Université Paris 7.
6. Hurkens, A. J. C. (1995). *A Simplification of Girard's Paradox.* TLCA 1995.
7. de Bruijn, N. (1972). *Lambda Calculus Notation with Nameless Dummies.*
8. Martin-Löf, P. (1984). *Intuitionistic Type Theory.* Bibliopolis.
9. Felicissimo, T. (2023). *Generic Bidirectional Typing for Dependent Type Theories.*
