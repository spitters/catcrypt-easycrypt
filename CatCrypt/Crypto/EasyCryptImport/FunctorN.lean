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
so an application is Lean application — `lowerFunctorNX ρ fuel F X Y` — and a
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
noncomputable def lowerParamsX (fuel : Nat) (M : EcModule) :
    (ps : EcParams) → ProcEnv → EcParamsFn ps (ModuleImpl M.interface)
  | [], ρ => lowerModule ρ fuel M
  | (x, I) :: ps, ρ => fun X : ModuleImpl I => lowerParamsX fuel M ps (ρ.bindModuleX x X)

theorem lowerParamsX_nil (fuel : Nat) (M : EcModule) (ρ : ProcEnv) :
    lowerParamsX fuel M [] ρ = lowerModule ρ fuel M := rfl

theorem lowerParamsX_cons (fuel : Nat) (M : EcModule) (x : String)
    (I : EcInterface) (ps : EcParams) (ρ : ProcEnv) (X : ModuleImpl I) :
    lowerParamsX fuel M ((x, I) :: ps) ρ X
      = lowerParamsX fuel M ps (ρ.bindModuleX x X) := rfl

/-- Lower a functor of several parameters to a curried Lean function on module
records. Functor application is function application, and a partial application
is the function awaiting the remaining modules. -/
noncomputable def lowerFunctorNX (ρ : ProcEnv) (fuel : Nat) (F : EcFunctorN) :
    EcParamsFn F.params (ModuleImpl F.body.interface) :=
  lowerParamsX fuel F.body F.params ρ

/-- A functor of one parameter lowers to the same function through either
route. -/
theorem lowerFunctorNX_toN (ρ : ProcEnv) (fuel : Nat) (F : EcFunctor) :
    lowerFunctorNX ρ fuel F.toN = lowerFunctorX ρ fuel F := rfl

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
      let S ← decodeStructureBody T baseId name mpath modJ
      .ok { name := name, params := ps, body := moduleOfStructure S }

/-- Decode the functor `name` from an exporter envelope, with the globals of its
body at location ids from `baseId` upwards. -/
def importFunctorN (T : DecodeTables) (name : String) (j : Json)
    (baseId : Nat := 0) : Except String EcFunctorN := do
  let e ← decodeEnvelope j
  let it ← findItem e name
  decodeFunctorN T baseId it

end CatCrypt.Crypto.EasyCryptImport
