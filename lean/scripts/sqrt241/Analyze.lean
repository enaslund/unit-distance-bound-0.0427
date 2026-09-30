/-
Taint analysis for the ℚ(√241) geometric port.

Run from `lean-formalization/` (the file is not part of any library):

  SQRT241_ANALYSIS_OUT=scripts/sqrt241/geometry_analysis.json \
    ./.toolchain/bin/lake env ./.toolchain/bin/lean scripts/sqrt241/Analyze.lean

The committed `geometry_analysis.json` is its output on the ℚ package of
2026-09-29; `regenerate_geometry.sh` reads it.

A declaration of the development is *witness-tainted* if its type (or, for a
definition, its value) mentions a constant of `UnitDistance.Witness`,
`UnitDistance.increment`/`exponent`, or the type `Fin 11`, directly or through
tainted declarations; it is *seven-tainted* if it lives in one of the √7
entireness modules and its type (or value) mentions the literal 7 or a
seven-tainted declaration. Starting from the ℚ bridge theorem, the traversal
follows tainted constants through types and values, stopping at the cut list
(the margin lemmas and the retained-field Galois lemmas, replaced by hand).
The output lists the collected constants with their modules; it is the input
of `copy_geometry.py`.
-/
module

import all UnitDistance.SharperPairFixedBaseBridgeRun20260920
public meta import Lean.Elab.Command

meta section

open Lean Meta Elab Command

def baseList : List Name := [`UnitDistance.increment, `UnitDistance.exponent]

def sevenMods : List String := ["UnitDistance.QuadraticSeven", "UnitDistance.ImaginarySeven",
  "UnitDistance.HeckeSigned", "UnitDistance.HeckeQuadraticContinuation",
  "UnitDistance.ImaginaryQuadraticContinuation"]

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `none

def isUD (env : Environment) (n : Name) : Bool :=
  (`UnitDistance).isPrefixOf (modOf env n)

def inSevenMod (env : Environment) (n : Name) : Bool :=
  let m := (modOf env n).toString
  sevenMods.any (fun p => p.isPrefixOf m)

def hasSeven (e : Expr) : Bool :=
  (e.find? (fun e => match e with
    | .lit (.natVal 7) => true
    | _ => false)).isSome

def relevantMods : List String := ["UnitDistance.ArithmeticSequence", "UnitDistance.FiniteFunctionalArithmetic", "UnitDistance.GaloisFixedArithmetic", "UnitDistance.GaussianMoments", "UnitDistance.GaussianProfiles", "UnitDistance.GaussianWindows", "UnitDistance.HeckeQuadraticContinuation", "UnitDistance.HeckeSignedArithmetic", "UnitDistance.HeckeSignedBochner", "UnitDistance.HeckeSignedEntire", "UnitDistance.HeckeSignedMassDifference", "UnitDistance.HeckeSignedMellinAgreement", "UnitDistance.HeckeSignedMellinClass", "UnitDistance.HeckeSignedMellinFinite", "UnitDistance.HeckeSignedMellinLattice", "UnitDistance.HeckeSignedMellinOrbit", "UnitDistance.HeckeSignedMellinTotal", "UnitDistance.HeckeSignedOddSupport", "UnitDistance.HeckeSignedThetaIdentities", "UnitDistance.ImaginaryQuadraticContinuation", "UnitDistance.ImaginarySevenUnramified", "UnitDistance.LocalOneDimensionalProfiles", "UnitDistance.QuadraticSevenConjugation", "UnitDistance.QuadraticSevenDescent", "UnitDistance.QuadraticSevenField", "UnitDistance.QuadraticSevenIntegrality", "UnitDistance.QuadraticSevenNormCongruence", "UnitDistance.RelativeArithmeticAmplitude", "UnitDistance.RelativeFieldEnergy", "UnitDistance.RelativeFieldProfile", "UnitDistance.RelativeWitnessAmplitude", "UnitDistance.SIntegerMixedCoordinates", "UnitDistance.SIntegerMixedInvariance", "UnitDistance.SIntegerMixedOverlap", "UnitDistance.SIntegerPairedCoordinates", "UnitDistance.SIntegerProfileBound", "UnitDistance.SIntegerReferenceFiniteSteps", "UnitDistance.SIntegerReferenceRescaling", "UnitDistance.SIntegerWitnessConcentration", "UnitDistance.SIntegerWitnessGraph", "UnitDistance.SIntegerWitnessModel", "UnitDistance.SIntegerWitnessPeriodSeparation", "UnitDistance.SIntegerWitnessProfile", "UnitDistance.SIntegerWitnessVertices", "UnitDistance.SIntegerWitnessWindow", "UnitDistance.SharperPairArithmeticRateCoreRun20260920", "UnitDistance.SharperPairFixedBaseBridgeRun20260920", "UnitDistance.SharperPairFixedBaseCoreRun20260920", "UnitDistance.StudentComplexCoordinates", "UnitDistance.StudentComplexDecay", "UnitDistance.StudentComplexExtension", "UnitDistance.StudentComplexIntegral", "UnitDistance.StudentComplexMajorant", "UnitDistance.StudentComplexRealRestriction", "UnitDistance.StudentComplexSlices", "UnitDistance.StudentComplexTubeSegments", "UnitDistance.StudentFourierEnvelope", "UnitDistance.StudentFourierIntegrand", "UnitDistance.StudentFourierShift", "UnitDistance.StudentFourierSlices", "UnitDistance.StudentMoments", "UnitDistance.StudentOverlap", "UnitDistance.StudentProfiles", "UnitDistance.StudentSchwartzGrowth", "UnitDistance.StudentWindows", "UnitDistance.Target", "UnitDistance.TensorEnergy", "UnitDistance.TensorFieldCoordinates", "UnitDistance.TensorFiniteFunctional", "UnitDistance.TensorFiniteOverlap", "UnitDistance.TensorFiniteProfiles", "UnitDistance.TensorFourier", "UnitDistance.TensorFunctional", "UnitDistance.TensorLocalMoments", "UnitDistance.TensorMixedCoordinates", "UnitDistance.TensorMixedLabelConcentration", "UnitDistance.TensorMixedLabels", "UnitDistance.TensorMixedOverlap", "UnitDistance.TensorMixedSupport", "UnitDistance.TensorMixedVolume", "UnitDistance.TensorOverlapCoordinates", "UnitDistance.TensorOverlapLaw", "UnitDistance.TensorOverlapMoments", "UnitDistance.TensorPhaseInvariance", "UnitDistance.Witness", "UnitDistance.WitnessFourierConstants", "UnitDistance.WitnessLocalFunctional", "UnitDistance.WitnessPeriodSeparation", "UnitDistance.WitnessPrimePairs"]

structure St where
  wmemo : Std.HashMap Name Bool := {}
  smemo : Std.HashMap Name Bool := {}

def usedOf (ci : ConstantInfo) : Array Name × Array Name :=
  let tyConsts := ci.type.getUsedConstants
  let valConsts : Array Name := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray
    | .ctorInfo d => #[d.induct]
    | _ => #[]
  (tyConsts, valConsts)

def hasFin11 (e : Expr) : Bool :=
  (e.find? (fun e => match e with
    | .app (.const `Fin _) a => (a.find? (fun x => match x with
        | .lit (.natVal 11) => true
        | _ => false)).isSome
    | _ => false)).isSome

def isBaseW (env : Environment) (n : Name) : Bool :=
  baseList.contains n || modOf env n == `UnitDistance.Witness

partial def wtaint (env : Environment) (n : Name) : StateM St Bool := do
  if isBaseW env n then return true
  if !isUD env n then return false
  if let some b := (← get).wmemo[n]? then return b
  modify fun s => { s with wmemo := s.wmemo.insert n false }
  let some ci := env.find? n | return false
  let (a, b) := usedOf ci
  let mut r := hasFin11 ci.type || (match ci with
    | .defnInfo d => hasFin11 d.value
    | _ => false)
  if !r then
    for c in a ++ b do
      if ← wtaint env c then
        r := true
        break
  modify fun s => { s with wmemo := s.wmemo.insert n r }
  return r

partial def staint (env : Environment) (n : Name) : StateM St Bool := do
  if !inSevenMod env n then return false
  if let some b := (← get).smemo[n]? then return b
  modify fun s => { s with smemo := s.smemo.insert n false }
  let some ci := env.find? n | return false
  let mut r := hasSeven ci.type
  if !r then
    match ci with
    | .defnInfo d => r := hasSeven d.value
    | _ => pure ()
  if !r then
    let (a, b) := usedOf ci
    for c in a ++ b do
      if ← staint env c then
        r := true
        break
  modify fun s => { s with smemo := s.smemo.insert n r }
  return r

def cuts : List Name := [
  `UnitDistance.Witness.sharperFixedBaseGap_le_shiftedMargin_run20260920,
  `UnitDistance.Witness.uniform_margin_sharper_astra,
  `UnitDistance.RelativeUnits.sharperFixedBaseGap_le_arithmeticRate_run20260920,
  `UnitDistance.Witness.sharperFixedBaseCeilingRun20260920,
  `UnitDistance.GaloisConjugation.fixedField_signature_lower,
  `UnitDistance.GaloisConjugation.totallyComplex_of_retained,
  `UnitDistance.GaloisConjugation.fixedField_finiteUnramified,
  `UnitDistance.GaloisConjugation.fixedField_rootDiscriminant_eq]

def tops : List Name := [
  `UnitDistance.SIntegerCRT.target_of_growing_retained_galois_fields_sharperFixedBase_run20260920,
  `UnitDistance.ImaginarySeven.finiteUnramified_of_real_place,
  `UnitDistance.QuadraticSeven.fixedRoot_sq,
  `UnitDistance.QuadraticSeven.exists_root_of_positive_real_places]

partial def collect (env : Environment) : StateM St (Array (Name × Name × String)) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Name) := (tops.map (·, `root)).toArray
  let mut out : Array (Name × Name × String) := #[]
  while !stack.isEmpty do
    let (n, par) := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let w ← wtaint env n
    let s ← staint env n
    let kind := (if w then "W" else "") ++ (if s then "S" else "") ++
      (if cuts.contains n then "C" else "") ++ (if isBaseW env n then "B" else "")
    out := out.push (n, par, kind)
    if cuts.contains n then continue
    if isBaseW env n then continue
    let some ci := env.find? n | continue
    let cs := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants | none => #[]) ++
      (match ci with
       | .inductInfo d => d.ctors.toArray
       | _ => #[])
    for c in cs do
      if (← wtaint env c) || (← staint env c) then stack := stack.push (c, n)
  return out

elab "#analyze" : command => do
  -- Inspect the same complete imported declarations as the original non-module script.
  -- A module's regular environment hides proof bodies in transitive imports.
  let env ← Lean.importModules
    #[{module := `UnitDistance.SharperPairFixedBaseBridgeRun20260920}]
    (← getOptions) (loadExts := false) (level := .private)
  let ((out, st)) := (collect env).run {}
  let arr := out.map fun (n, p, k) =>
    Json.mkObj [("name", toJson n.toString), ("parent", toJson p.toString),
      ("kind", toJson k), ("module", toJson (modOf env n).toString)]
  -- full witness taint list over UD constants in relevant modules
  let mut tainted : Array Json := #[]
  let (_, st2) := (do
      for (n, _) in env.constants.map₁.toList do
        if relevantMods.contains (modOf env n).toString then
          let _ ← wtaint env n
          let _ ← staint env n
      pure () : StateM St Unit).run st
  for (n, b) in st2.wmemo.toList do
    if b then tainted := tainted.push (toJson n.toString)
  let mut stainted : Array Json := #[]
  for (n, b) in st2.smemo.toList do
    if b then stainted := stainted.push (toJson n.toString)
  let j := Json.mkObj [("collected", Json.arr arr), ("wtainted", Json.arr tainted),
    ("stainted", Json.arr stainted)]
  let outPath := (← IO.getEnv "SQRT241_ANALYSIS_OUT").getD "sqrt241-analysis.json"
  IO.FS.writeFile outPath j.compress
  logInfo m!"collected {out.size}, wtainted {tainted.size}, stainted {stainted.size}"

#analyze
