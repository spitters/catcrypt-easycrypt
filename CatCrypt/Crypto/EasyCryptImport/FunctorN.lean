/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json
import CatCrypt.Crypto.EasyCryptImport.Lower

/-!
# EasyCrypt import: functors of several parameters

An EasyCrypt module may bind any number of module parameters, and the export
carries them as a list: one entry per parameter, in declaration order, each an
identifier together with the module type it must implement. A call to the
parameter `X`'s procedure `p` inside the body is the cross-path `X./p`, so the
parameters are told apart by their source names and each occupies its own prefix
of the call-resolution namespace.

`EcFunctorN` is that shape: a name, the parameter list `EcParams`, and one body
module. `EcFunctor` — a functor of one parameter — is the special case, and
`EcFunctor.toN` embeds it (`lowerFunctorNX_toN`).

## The lowering is curried

`EcParamsFn` sends a parameter list and a result type to the type of a curried
function taking one `ModuleImpl` per parameter, at the interface that parameter
declares. `lowerFunctorNX` lands in
`EcParamsFn F.params (ModuleImpl F.body.interface)`,
so an application is Lean application — `lowerFunctorNX ρ ω fuel F X Y` — and a
partial application is a Lean function awaiting the remaining modules. Each
parameter is bound with `ProcEnv.bindModuleX` under its own name as the body
reaches it, which is what a decoded body's cross-paths resolve against, and the
body is lowered once every parameter is bound.

## Two parameters of one source name have no image

EasyCrypt does not reject `module F (P : I) (P : J)`, and the export writes both
parameters under the name `P` while the body's call stays the bare cross-path
`P./p`. Binding both with `bindModuleX "P"` would make one shadow the other, and
the cross-path carries no stamp to say which the call means, so `decodeParamsN`
rejects a repeated parameter name.

## Parameterised module types

A module type may bind module parameters too — `module type Adversary (O :
Oracle)` — and the export carries them in the type's `sig`, at the same shape a
module's parameter list has. `EcModTypeN` is the image: the parameter list
`EcParams` and the interface of the type's own procedures. A module parameter is
not a type, so no procedure signature can mention one: the interface of a
parameterised module type is the same plain procedure list an unparameterised
one has, and what the parameters scope in EasyCrypt — which of their oracles
each procedure may call, the export's `oinfos` — is not carried by the decode.
A functor parameter declared at a parameterised module type resolves the same
way: `decodeModTypeSig` reads the type's procedure list and drops its parameter
list, so `decodeParamsN` accepts such a parameter.

## An applied module bound to a name does not decode

`module G = F(M)` and `module G (X : I) = F(X, M)` export with the body kind
`ME_Alias`, whose target is the applied module path as a string and whose `arity`
counts the parameters the alias itself binds; the parameters after those are the
target's residual ones, carried verbatim. No body sits behind the alias, so
`decodeStructureBody` rejects the node by its body kind. A statement that names
an application — `Top.F(A, Top.M)./p` — reaches the importer as that path, and
the image it denotes is supplied by the caller through `FormEnv.functorImages`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)
open CatCrypt.Core

/-! ## Syntax -/

/-- The parameters a functor binds: the source name and the required interface of
each, in the order the functor declares them. -/
abbrev EcParams := List (String × EcInterface)

/-- The type of a curried function taking one module per parameter of `ps`, at the
interface that parameter declares, and returning `R`. -/
def EcParamsFn : EcParams → Type → Type
  | [], R => R
  | (_, I) :: ps, R => ModuleImpl I → EcParamsFn ps R

theorem EcParamsFn_nil (R : Type) : EcParamsFn [] R = R := rfl

theorem EcParamsFn_cons (x : String) (I : EcInterface) (ps : EcParams) (R : Type) :
    EcParamsFn ((x, I) :: ps) R = (ModuleImpl I → EcParamsFn ps R) := rfl

/-- A parameterised module `F(X₁ : I₁) … (Xₙ : Iₙ)`: the body is a module whose
procedures may call each parameter's procedures under that parameter's own
prefix. -/
structure EcFunctorN where
  /-- The functor name (provenance). -/
  name : String
  /-- The parameters, in declaration order. -/
  params : EcParams
  /-- The functor body. -/
  body : EcModule

/-- A functor of one parameter as an `EcFunctorN`. -/
def EcFunctor.toN (F : EcFunctor) : EcFunctorN where
  name := F.name
  params := [(F.paramName, F.paramInterface)]
  body := F.body

/-! ## Lowering -/

/-- Lower the module `M` under a parameter list: bind each parameter with
`ProcEnv.bindModuleX` under its own name as its module arrives, and lower `M`
against the environment once no parameter is left. -/
noncomputable def lowerParamsX (ω : OpEnv) (fuel : Nat) (M : EcModule) :
    (ps : EcParams) → ProcEnv → EcParamsFn ps (ModuleImpl M.interface)
  | [], ρ => lowerModule ρ ω fuel M
  | (x, I) :: ps, ρ => fun X : ModuleImpl I => lowerParamsX ω fuel M ps (ρ.bindModuleX x X)

theorem lowerParamsX_nil (ω : OpEnv) (fuel : Nat) (M : EcModule) (ρ : ProcEnv) :
    lowerParamsX ω fuel M [] ρ = lowerModule ρ ω fuel M := rfl

theorem lowerParamsX_cons (ω : OpEnv) (fuel : Nat) (M : EcModule) (x : String)
    (I : EcInterface) (ps : EcParams) (ρ : ProcEnv) (X : ModuleImpl I) :
    lowerParamsX ω fuel M ((x, I) :: ps) ρ X
      = lowerParamsX ω fuel M ps (ρ.bindModuleX x X) := rfl

/-- Lower a functor of several parameters to a curried Lean function on module
records. Functor application is function application, and a partial application
is the function awaiting the remaining modules. -/
noncomputable def lowerFunctorNX (ρ : ProcEnv) (ω : OpEnv) (fuel : Nat) (F : EcFunctorN) :
    EcParamsFn F.params (ModuleImpl F.body.interface) :=
  lowerParamsX ω fuel F.body F.params ρ

/-- A functor of one parameter lowers to the same function through either
route. -/
theorem lowerFunctorNX_toN (ρ : ProcEnv) (ω : OpEnv) (fuel : Nat) (F : EcFunctor) :
    lowerFunctorNX ρ ω fuel F.toN = lowerFunctorX ρ ω fuel F := rfl

/-! ## Decoding -/

/-- Decode the `params` list of a module item: each entry's identifier is the
prefix its body calls the parameter by, and its interface is the module type the
parameter is declared at. A parameter name that repeats is rejected, since the
cross-path a call writes carries the name alone. -/
def decodeParamsN (T : DecodeTables) (name : String) :
    List Json → Except String EcParams
  | [] => .ok []
  | pJ :: rest => do
    let pname ← getIdent pJ "name"
    let mtJ ← getObj pJ "modtype"
    let I ← decodeModTypeSig T mtJ
    let ps ← decodeParamsN T name rest
    if ps.any (fun p => p.1 == pname) then
      fail s!"module '{name}' binds two parameters named '{pname}': a call to a \
        parameter is the cross-path '{pname}./p', which carries no stamp to say \
        which of the two it means"
    else
      .ok ((pname, I) :: ps)

/-- Decode a `Th_module` item that takes at least one module parameter as an
`EcFunctorN`. The body must be an `ME_Structure`: a module defined as an
application of another has an `ME_Alias` body, which `decodeStructureBody` rejects
by kind. -/
def decodeFunctorN (T : DecodeTables) (baseId : Nat) (j : Json) :
    Except String EcFunctorN := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_module" then
    fail s!"theory item of kind '{kind}': only Th_module has a functor image"
  else
    let name ← getStr j "name"
    let mpath ← getStr j "path"
    let modJ ← getObj j "module"
    let paramsA ← getArr modJ "params"
    if paramsA.isEmpty then
      fail s!"module '{name}' takes no parameter, so it is a module rather than a \
        functor: decode it with decodeModule"
    else
      let ps ← decodeParamsN T name paramsA.toList
      -- Every parameter's procedures are resolvable inside the body, keyed by
      -- the cross-paths its calls write; a call that discards its result reads
      -- its signature there.
      let S ← decodeStructureBody
        (ps.foldl (fun T p => T.withInterfaceX p.1 p.2) T) baseId name mpath modJ
      .ok { name := name, params := ps, body := moduleOfStructure S }

/-- Decode the functor `name` from an exporter envelope, with the globals of its
body at location ids from `baseId` upwards. -/
def importFunctorN (T : DecodeTables) (name : String) (j : Json)
    (baseId : Nat := 0) : Except String EcFunctorN := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeFunctorN T baseId it

/-! ## Parameterised module types -/

/-- A parameterised module type `MT(X₁ : I₁) … (Xₙ : Iₙ)`: the parameters and
the interface of the type's own procedures. The parameters do not occur in the
procedure signatures — a module parameter is not a type — so the interface is
the same shape an unparameterised module type has; see the module docstring for
what the parameters scope in EasyCrypt and what the decode does not carry. -/
structure EcModTypeN where
  /-- The module type's name (provenance). -/
  name : String
  /-- The parameters, in declaration order. -/
  params : EcParams
  /-- The procedures a module of this type offers. -/
  interface : EcInterface

/-- Decode a `Th_modtype` item that binds at least one module parameter. The
parameters decode as a functor's do (`decodeParamsN`), and the procedures decode
through `decodeModSigProcs`. -/
def decodeModTypeN (T : DecodeTables) (j : Json) : Except String EcModTypeN := do
  let k ← getStr j "kind"
  if k ≠ "Th_modtype" then
    fail s!"item of kind '{k}' read as a module type"
  else
    let name ← getStr j "name"
    let sigJ ← getObj j "sig"
    let paramsA ← getArr sigJ "params"
    if paramsA.isEmpty then
      fail s!"module type '{name}' binds no parameter: decode it with \
        decodeModTypeInterface"
    else
      let ps ← decodeParamsN T name paramsA.toList
      let I ← decodeModSigProcs T sigJ
      .ok { name := name, params := ps, interface := I }

/-- Decode the parameterised module type `name` from an exporter envelope. -/
def importModTypeN (T : DecodeTables) (name : String) (j : Json) :
    Except String EcModTypeN := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeModTypeN T it

/-! ## Golden tests

The checks below decode an inline parameterised module type of the
`crypto/PRG.eca` shape — a `Distinguisher (G : RGA)` whose parameter's `next`
returns an abstract type — following the `#guard` pattern of `Json.lean`. -/

section Golden

/-- A nullary type node at the path `p`. -/
private def jTyAt (p : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str p),
              ("args", Json.arr #[])]

/-- A procedure signature declaration with no named formal parameter, from the
type at `argPath` to the type at `retPath`. -/
private def jProcDecl (name argPath retPath : String) : Json :=
  Json.mkObj [("name", Json.str name),
              ("sig", Json.mkObj
                [("args", Json.arr #[]),
                 ("argty", jTyAt argPath), ("ret", jTyAt retPath)])]

/-- A module-type parameter `name : mtName`, whose module type declares
`procs`. -/
private def jModTypeParam (name mtName : String) (procs : Array Json) : Json :=
  Json.mkObj [("name", Json.str name), ("stamp", Json.num 7),
              ("modtype", Json.mkObj
                [("kind", Json.str "ModuleType"), ("name", Json.str mtName),
                 ("params", Json.arr #[]), ("args", Json.arr #[]),
                 ("sig", Json.mkObj
                   [("params", Json.arr #[]), ("procs", Json.arr procs)])])]

/-- The signature of `module type Distinguisher (G : RGA)`, where `RGA` declares
`next : unit -> output` at the abstract type `Top.output` and the type's own
procedure is `distinguish : unit -> bool`. -/
private def jDistinguisherSig : Json :=
  Json.mkObj
    [("params", Json.arr
       #[jModTypeParam "G" "Top.RGA"
           #[jProcDecl "next" "Top.Pervasive.unit" "Top.output"]]),
     ("procs", Json.arr
       #[jProcDecl "distinguish" "Top.Pervasive.unit" "Top.Pervasive.bool"])]

/-- The `Th_modtype` item declaring that `Distinguisher`. -/
private def jDistinguisher : Json :=
  Json.mkObj
    [("kind", Json.str "Th_modtype"), ("name", Json.str "Distinguisher"),
     ("path", Json.str "Top.Distinguisher"),
     ("sig", jDistinguisherSig)]

-- The parameterised module type decodes once the abstract type its parameter
-- mentions is registered: one parameter at the declared interface, and the
-- type's own procedure list.
#guard (match decodeModTypeN (ecPrelude.withOpaqueType "Top.output")
            jDistinguisher with
        | .ok MT =>
          MT.name == "Distinguisher"
            && (match MT.params with
                | [(pn, I)] =>
                  pn == "G" && I.names == ["next"]
                    && I.sig "next"
                        == { arg := .unit, res := .opaque "Top.output" }
                | _ => false)
            && MT.interface.names == ["distinguish"]
            && MT.interface.sig "distinguish" == { arg := .unit, res := .bool }
        | _ => false)

-- Against the default tables the same item is rejected: the parameter's `next`
-- returns a type outside the type table.
#guard (match decodeModTypeN ecPrelude jDistinguisher with
        | .error _ => true
        | _ => false)

-- `decodeModTypeInterface` still rejects the parameterised item: its image is
-- an `EcModTypeN`, not a bare `EcInterface`.
#guard (match decodeModTypeInterface (ecPrelude.withOpaqueType "Top.output")
            jDistinguisher with
        | .error _ => true
        | _ => false)

/-- A functor parameter `D` declared at the parameterised `Distinguisher`. -/
private def jParamDistinguisher : Json :=
  Json.mkObj [("name", Json.str "D"), ("stamp", Json.num 9),
              ("modtype", Json.mkObj
                [("kind", Json.str "ModuleType"),
                 ("name", Json.str "Top.Distinguisher"),
                 ("params", Json.arr #[]), ("args", Json.arr #[]),
                 ("sig", jDistinguisherSig)])]

-- A functor parameter whose module type is itself parameterised resolves to
-- that type's procedure list.
#guard (match decodeParamsN (ecPrelude.withOpaqueType "Top.output") "IND"
            [jParamDistinguisher] with
        | .ok [(pn, I)] =>
          pn == "D" && I.names == ["distinguish"]
            && I.sig "distinguish" == { arg := .unit, res := .bool }
        | _ => false)

end Golden

end CatCrypt.Crypto.EasyCryptImport
