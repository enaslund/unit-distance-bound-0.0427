module

public import UnitDistance.Sqrt241.GroupData.Retained
public import UnitDistance.ClassTwoTameWords
public import UnitDistance.DyadicClosedPresentation
public import UnitDistance.GroupAugmentationWordDegrees
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-!
# The thirty literal cut words over `ℚ(√241)`

For lifts of the local generators in any group (complex conjugations
`c₁, c₂`; tame inertia and Frobenius at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`; dyadic `x, y, z`
at `𝔭₁, 𝔭₂`; the caps Frob(29₁), Frob(29₂), F₇²) the cut consists of

* 21 quadratic words: `c₁², c₂²`, the four tame words `φτφ⁻¹τ^{-N}`, `y₂²`,
  `x_P², [x_P,y_P], [x_P,z_P]` (`P = 1, 2`), the squares `τ², φ²`;
* 2 cubic words `[[y_P,z_P],z_P]`;
* 7 deep words `z_P⁴, [y_P,z_P]²` (`P = 1, 2`), `Frob(29₁)⁴, Frob(29₂)⁴, (F₇²)⁴`.

At `𝔭₁` the square `y₁²` is not a word (the genuine relation replaces it).
When the lifts have the elementary vectors of construction.md §3.4 in the
retained model `Q_B`, every word dies there (`closedNormalClosure_le_ker`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241
open ClassTwo GroupData
open Dyadic.Presentation (comm literalRelations)

/-- Lifts of the local generators in a group `G`. Index conventions: `P = 0, 1`
for `𝔭₁, 𝔭₂`; `q = 0, 1, 2, 3` for `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`; caps `k = 0, 1, 2` for
Frob(29₁), Frob(29₂), F₇². -/
structure Lifts (G : Type*) [Group G] where
  conj : Fin 2 → G
  tameInertia : Fin 4 → G
  tameFrobenius : Fin 4 → G
  dyadicX : Fin 2 → G
  dyadicY : Fin 2 → G
  dyadicZ : Fin 2 → G
  cap : Fin 3 → G

namespace Lifts
variable {G H : Type*} [Group G] [Group H]

/-- The image of the lifts under a homomorphism. -/
def map (f : G →* H) (L : Lifts G) : Lifts H where
  conj i := f (L.conj i)
  tameInertia q := f (L.tameInertia q)
  tameFrobenius q := f (L.tameFrobenius q)
  dyadicX P := f (L.dyadicX P)
  dyadicY P := f (L.dyadicY P)
  dyadicZ P := f (L.dyadicZ P)
  cap k := f (L.cap k)

/-- The tame word `φ τ φ⁻¹ (τ^N)⁻¹`. -/
def tameWord (N : ℕ) (t f : G) : G := f*t*f⁻¹*(t^N)⁻¹

/-- The 21 quadratic words. -/
def quadraticWords (L : Lifts G) : Fin 21 → G :=
  ![L.conj 0^2,L.conj 1^2,
    tameWord (tameNorm 0) (L.tameInertia 0) (L.tameFrobenius 0),
    tameWord (tameNorm 1) (L.tameInertia 1) (L.tameFrobenius 1),
    tameWord (tameNorm 2) (L.tameInertia 2) (L.tameFrobenius 2),
    tameWord (tameNorm 3) (L.tameInertia 3) (L.tameFrobenius 3),
    L.dyadicY 1^2,
    L.dyadicX 0^2,comm (L.dyadicX 0) (L.dyadicY 0),comm (L.dyadicX 0) (L.dyadicZ 0),
    L.dyadicX 1^2,comm (L.dyadicX 1) (L.dyadicY 1),comm (L.dyadicX 1) (L.dyadicZ 1),
    L.tameInertia 0^2,L.tameInertia 1^2,L.tameInertia 2^2,L.tameInertia 3^2,
    L.tameFrobenius 0^2,L.tameFrobenius 1^2,L.tameFrobenius 2^2,L.tameFrobenius 3^2]

/-- The two cubic dyadic words `[[y_P,z_P],z_P]`. -/
def cubicWords (L : Lifts G) : Fin 2 → G :=
  fun P => comm (comm (L.dyadicY P) (L.dyadicZ P)) (L.dyadicZ P)

/-- The seven deep words. -/
def deepWords (L : Lifts G) : Fin 7 → G :=
  ![L.dyadicZ 0^4,(comm (L.dyadicY 0) (L.dyadicZ 0))^2,
    L.dyadicZ 1^4,(comm (L.dyadicY 1) (L.dyadicZ 1))^2,
    L.cap 0^4,L.cap 1^4,L.cap 2^4]

/-- The literal cut: thirty words. -/
def words (L : Lifts G) : Set G :=
  Set.range L.quadraticWords ∪ Set.range L.cubicWords ∪ Set.range L.deepWords

theorem map_tameWord (f : G →* H) (N : ℕ) (t g : G) :
    f (tameWord N t g) = tameWord N (f t) (f g) := by
  simp [tameWord,map_mul,map_inv,map_pow]

theorem map_quadraticWords (f : G →* H) (L : Lifts G) (i : Fin 21) :
    f (L.quadraticWords i) = (L.map f).quadraticWords i := by
  fin_cases i <;> simp [quadraticWords,map,map_pow,map_tameWord]

theorem map_cubicWords (f : G →* H) (L : Lifts G) (P : Fin 2) :
    f (L.cubicWords P) = (L.map f).cubicWords P := by
  simp [cubicWords,map]

theorem map_deepWords (f : G →* H) (L : Lifts G) (i : Fin 7) :
    f (L.deepWords i) = (L.map f).deepWords i := by
  fin_cases i <;> simp [deepWords,map,map_pow]

theorem deepWords_mem_dimension_four (L : Lifts G) (i : Fin 7) :
    L.deepWords i ∈ GroupAugmentation.dimensionSubgroup F G 4 := by
  fin_cases i
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G _
  · exact GroupAugmentation.commutator_square_mem_dimension_four F G _ _
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G _
  · exact GroupAugmentation.commutator_square_mem_dimension_four F G _ _
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G _
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G _
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G _

/-- The elementary label facts: `e` of each lift is the vector of §3.4. -/
structure Labels (L : Lifts G) (e : G → V) : Prop where
  conj : ∀ i, e (L.conj i) = conjVector i
  tameInertia : ∀ q, e (L.tameInertia q) = tameInertiaVector q
  tameFrobenius : ∀ q, e (L.tameFrobenius q) = tameFrobeniusVector q
  dyadicX : ∀ P, e (L.dyadicX P) = dyadicXVector P
  dyadicY : ∀ P, e (L.dyadicY P) = dyadicYVector P
  dyadicZ : ∀ P, e (L.dyadicZ P) = dyadicZVector P
  cap : ∀ k, e (L.cap k) = capVector k

theorem Labels.map {L : Lifts G} {e : H → V} (f : G →* H) (h : (L.map f).Labels e) :
    L.Labels (e ∘ f) :=
  ⟨h.conj,h.tameInertia,h.tameFrobenius,h.dyadicX,h.dyadicY,h.dyadicZ,h.cap⟩

theorem Labels.of_map {L : Lifts G} {e : H → V} (f : G →* H) (h : L.Labels (e ∘ f)) :
    (L.map f).Labels e :=
  ⟨h.conj,h.tameInertia,h.tameFrobenius,h.dyadicX,h.dyadicY,h.dyadicZ,h.cap⟩

end Lifts

namespace Retained

def squareForm (v : V) : W := cocycle v v
def bracketForm (v w : V) : W := cocycle v w-cocycle w v
def tameForm (q : Fin 4) : W :=
  bracketForm (tameInertiaVector q) (tameFrobeniusVector q) +
    (if tameNorm q % 4 = 3 then 1 else 0 : F) • squareForm (tameInertiaVector q)

/-- Central coordinates of the 21 quadratic words in `Q_B`. -/
def forms : Fin 21 → W :=
  ![squareForm (conjVector 0),squareForm (conjVector 1),tameForm 0,tameForm 1,tameForm 2,
    tameForm 3,squareForm (dyadicYVector 1),
    squareForm (dyadicXVector 0),bracketForm (dyadicXVector 0) (dyadicYVector 0),
    bracketForm (dyadicXVector 0) (dyadicZVector 0),
    squareForm (dyadicXVector 1),bracketForm (dyadicXVector 1) (dyadicYVector 1),
    bracketForm (dyadicXVector 1) (dyadicZVector 1),
    squareForm (tameInertiaVector 0),squareForm (tameInertiaVector 1),
    squareForm (tameInertiaVector 2),squareForm (tameInertiaVector 3),
    squareForm (tameFrobeniusVector 0),squareForm (tameFrobeniusVector 1),
    squareForm (tameFrobeniusVector 2),squareForm (tameFrobeniusVector 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- All 21 quadratic cut forms vanish in the retained model (checked one form at a
time, so that every kernel reduction stays small). -/
theorem forms_zero_certificate : ∀ (i : Fin 21) (k : Fin 15), forms i k = 0 := by
  intro i
  fin_cases i <;> decide +kernel

theorem forms_zero (i : Fin 21) : forms i = 0 := funext (forms_zero_certificate i)

theorem tameNorm_odd (q : Fin 4) : tameNorm q % 4 = 1 ∨ tameNorm q % 4 = 3 := by
  have h : ∀ q : Fin 4, tameNorm q % 4 = 1 ∨ tameNorm q % 4 = 3 := by decide
  exact h q

theorem comm_coordinates (g h : Q) : comm g h = (⟨0,bracketForm g.base h.base⟩ : Q) :=
  GroupModel.commutator_coordinates cocycle g h

theorem sq_coordinates (g : Q) : g^2 = (⟨0,squareForm g.base⟩ : Q) :=
  GroupModel.square_coordinates cocycle g

theorem tameWord_coordinates (q : Fin 4) (t f : Q) :
    Lifts.tameWord (tameNorm q) t f = (⟨0,bracketForm t.base f.base+
      (if tameNorm q % 4 = 3 then 1 else 0 : F) • squareForm t.base⟩ : Q) :=
  ClassTwo.Tame.word_odd cocycle (tameNorm q) (tameNorm_odd q) t f

/-- The quadratic words of lifts with the specified vectors are the displayed
central elements. -/
theorem quadraticWords_coordinates (L : Lifts Q) (hL : L.Labels (fun g => g.base))
    (i : Fin 21) : L.quadraticWords i = (⟨0,forms i⟩ : Q) := by
  fin_cases i
  · change L.conj 0^2 = _; rw [sq_coordinates,hL.conj]; rfl
  · change L.conj 1^2 = _; rw [sq_coordinates,hL.conj]; rfl
  · change Lifts.tameWord (tameNorm 0) _ _ = _
    rw [tameWord_coordinates,hL.tameInertia,hL.tameFrobenius]; rfl
  · change Lifts.tameWord (tameNorm 1) _ _ = _
    rw [tameWord_coordinates,hL.tameInertia,hL.tameFrobenius]; rfl
  · change Lifts.tameWord (tameNorm 2) _ _ = _
    rw [tameWord_coordinates,hL.tameInertia,hL.tameFrobenius]; rfl
  · change Lifts.tameWord (tameNorm 3) _ _ = _
    rw [tameWord_coordinates,hL.tameInertia,hL.tameFrobenius]; rfl
  · change L.dyadicY 1^2 = _; rw [sq_coordinates,hL.dyadicY]; rfl
  · change L.dyadicX 0^2 = _; rw [sq_coordinates,hL.dyadicX]; rfl
  · change comm _ _ = _; rw [comm_coordinates,hL.dyadicX,hL.dyadicY]; rfl
  · change comm _ _ = _; rw [comm_coordinates,hL.dyadicX,hL.dyadicZ]; rfl
  · change L.dyadicX 1^2 = _; rw [sq_coordinates,hL.dyadicX]; rfl
  · change comm _ _ = _; rw [comm_coordinates,hL.dyadicX,hL.dyadicY]; rfl
  · change comm _ _ = _; rw [comm_coordinates,hL.dyadicX,hL.dyadicZ]; rfl
  · change L.tameInertia 0^2 = _; rw [sq_coordinates,hL.tameInertia]; rfl
  · change L.tameInertia 1^2 = _; rw [sq_coordinates,hL.tameInertia]; rfl
  · change L.tameInertia 2^2 = _; rw [sq_coordinates,hL.tameInertia]; rfl
  · change L.tameInertia 3^2 = _; rw [sq_coordinates,hL.tameInertia]; rfl
  · change L.tameFrobenius 0^2 = _; rw [sq_coordinates,hL.tameFrobenius]; rfl
  · change L.tameFrobenius 1^2 = _; rw [sq_coordinates,hL.tameFrobenius]; rfl
  · change L.tameFrobenius 2^2 = _; rw [sq_coordinates,hL.tameFrobenius]; rfl
  · change L.tameFrobenius 3^2 = _; rw [sq_coordinates,hL.tameFrobenius]; rfl

theorem quadraticWords_eq_one (L : Lifts Q) (hL : L.Labels (fun g => g.base)) (i : Fin 21) :
    L.quadraticWords i = 1 := by
  rw [quadraticWords_coordinates L hL,forms_zero]
  rfl

/-- The cubic words die in every class-two model. -/
theorem cubicWords_eq_one (L : Lifts Q) (P : Fin 2) : L.cubicWords P = 1 := by
  change comm (comm _ _) _ = 1
  rw [comm_coordinates,comm_coordinates]
  apply GroupModel.ext
  · rfl
  · change bracketForm 0 _ = 0
    simp [bracketForm]

theorem deepWords_eq_one (L : Lifts Q) (i : Fin 7) : L.deepWords i = 1 := by
  have h := L.deepWords_mem_dimension_four i
  have h3 := GroupAugmentation.dimensionSubgroup_antitone F Q (by decide : 3 ≤ 4) h
  rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at h3
  exact h3

theorem words_eq_one (L : Lifts Q) (hL : L.Labels (fun g => g.base)) (g : Q)
    (hg : g ∈ L.words) : g = 1 := by
  rcases hg with (⟨i,rfl⟩ | ⟨P,rfl⟩) | ⟨i,rfl⟩
  · exact quadraticWords_eq_one L hL i
  · exact cubicWords_eq_one L P
  · exact deepWords_eq_one L i

open ProCGroups ProCGroups.Presentations

/-- A continuous map to `Q_B` sending the lifts to the specified vectors kills
the whole closed normal cut kernel. -/
theorem closedNormalClosure_le_ker {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ρ : G →ₜ* Q) (L : Lifts G)
    (hL : L.Labels (fun g => (ρ g).base)) :
    closedNormalClosure L.words ≤ ρ.toMonoidHom.ker := by
  apply closedNormalClosure_le_closed_normal (ProCGroups.ContinuousMonoidHom.isClosed_ker ρ)
  intro g hg
  change ρ g = 1
  have hL' : (L.map ρ.toMonoidHom).Labels (fun g => g.base) := Lifts.Labels.of_map _ hL
  rcases hg with (⟨i,rfl⟩ | ⟨P,rfl⟩) | ⟨i,rfl⟩
  · exact (L.map_quadraticWords ρ.toMonoidHom i).trans (quadraticWords_eq_one _ hL' i)
  · exact (L.map_cubicWords ρ.toMonoidHom P).trans (cubicWords_eq_one _ P)
  · exact (L.map_deepWords ρ.toMonoidHom i).trans (deepWords_eq_one _ i)

end Retained
end UnitDistance.Sqrt241
