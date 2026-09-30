module

public import UnitDistance.TruncatedMagnusLinear
public import UnitDistance.ClassTwoCollection
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index

@[expose] public section
set_option backward.privateInPublic true


/-! A concrete family of 4096 distinct conjugates in an actual quotient of
the truncated Magnus group. Quadratic relator tails remain arbitrary. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus
open Group
variable {R : Type*} [CommRing R]

@[simp] theorem conjugate_first (g h : Group R) : (g*h*g⁻¹).first=h.first := by
  simp

theorem conjugate_second (g h : Group R) :
    (g*h*g⁻¹).second=fun i j => h.second i j+g.first i*h.first j-h.first i*g.first j := by
  ext i j
  simp
  ring

theorem conjugate_of_first_zero (g h : Group R) (hg : g.first=0) :
    g*h*g⁻¹=(⟨h.first,h.second,h.third-bracket h.first g.second⟩ : Group R) := by
  ext <;> simp [hg,bracket] <;> ring

theorem div_second_of_first_eq (g h : Group R) (hf : g.first=h.first) :
    (g/h).second=g.second-h.second := by
  ext i j
  simp [div_eq_mul_inv,hf]
  ring

theorem div_third_of_first_second_eq (g h : Group R)
    (hf : g.first=h.first) (hs : g.second=h.second) : (g/h).third=g.third-h.third := by
  ext i j k
  simp [div_eq_mul_inv,hf,hs]
  ring

namespace Certificate
open ClassTwo.Collection

abbrev Cut (tails : Fin 16 → V₃ F) := Group F ⧸ cutSubgroup tails

def quotientMap (tails : Fin 16 → V₃ F) : Group F →* Cut tails :=
  QuotientGroup.mk' (cutSubgroup tails)

theorem secondDetector_eq_of_quotient (tails : Fin 16 → V₃ F) (g h : Group F)
    (hf : g.first=h.first) (he : quotientMap tails g=quotientMap tails h) :
    secondDetector g.second=secondDetector h.second := by
  have hm : g/h∈cutSubgroup tails := QuotientGroup.eq_iff_div_mem.mp he
  obtain ⟨v,hv⟩ := hm.2.1
  have hz : secondDetector (g/h).second=0 := by
    rw [← hv]
    exact secondDetector_rowMap v
  rw [div_second_of_first_eq g h hf,map_sub,sub_eq_zero] at hz
  exact hz

theorem thirdDetector_eq_of_quotient (tails : Fin 16 → V₃ F) (g h : Group F)
    (hf : g.first=h.first) (hs : g.second=h.second)
    (he : quotientMap tails g=quotientMap tails h) :
    thirdDetector g.third=thirdDetector h.third := by
  have hm : g/h∈cutSubgroup tails := QuotientGroup.eq_iff_div_mem.mp he
  have hz := hm.2.2
  rw [div_second_of_first_eq g h hf,hs,sub_self,map_zero,
    div_third_of_first_second_eq g h hf hs,map_sub,sub_eq_zero] at hz
  exact hz

/-- Literal free-generator images in the truncated group. -/
def generator (i : Fin 7) : Group F := ⟨e i,0,0⟩

def sixIndices : List (Fin 6) := [0,1,2,3,4,5]

def baseWord (u : U) : Group F := word (fun i : Fin 6 => generator i.succ) sixIndices u

def quadraticGenerator (i : Fin 6) : Group F :=
  generator (selectedPairs i).1*generator (selectedPairs i).2*
    (generator (selectedPairs i).1)⁻¹*(generator (selectedPairs i).2)⁻¹

def quadraticWord (v : U) : Group F := word quadraticGenerator sixIndices v

theorem bit_first (g : Group F) (t : F) : (bit g t).first=t • g.first := by
  rcases binary_cases t with rfl | rfl <;> simp

theorem bit_second (g : Group F) (t : F) : (bit g t).second=t • g.second := by
  rcases binary_cases t with rfl | rfl <;> simp

@[simp] theorem quadraticGenerator_first (i : Fin 6) : (quadraticGenerator i).first=0 := by
  simp [quadraticGenerator]

@[simp] theorem quadraticGenerator_second (i : Fin 6) :
    (quadraticGenerator i).second=selectedQuadratic i := by
  funext j k
  simpa only [quadraticGenerator,generator,selectedQuadratic,quadraticBracket] using
    commutator_second (generator (selectedPairs i).1) (generator (selectedPairs i).2) j k

@[simp] theorem baseWord_first (u : U) : (baseWord u).first=baseMap u := by
  simp only [baseWord,word,sixIndices,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    mul_first,one_first,bit_first]
  change _=coordinateCombination (fun i : Fin 6 => e i.succ) u
  simp [coordinateCombination,Fin.sum_univ_succ,generator]

@[simp] theorem quadraticWord_first (v : U) : (quadraticWord v).first=0 := by
  simp [quadraticWord,word,sixIndices,bit_first]

@[simp] theorem quadraticWord_second (v : U) : (quadraticWord v).second=selectedMap v := by
  simp only [quadraticWord,word,sixIndices,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]
  funext i j
  simp [bit_first,bit_second,selectedMap,coordinateCombination,Fin.sum_univ_succ]

def conjugator (u v : U) : Group F := baseWord u*quadraticWord v

def conjugate (u v : U) : Group F := conjugator u v*generator 0*(conjugator u v)⁻¹

theorem quadraticBracket_comm (x y : V₁ F) : quadraticBracket x y=quadraticBracket y x := by
  ext i j
  simp [quadraticBracket,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_comm]

/-- The first six parameters are detected by the actual quadratic coordinate. -/
theorem conjugate_second_detect (u v : U) : secondDetector (conjugate u v).second=u := by
  have h : (conjugate u v).second=quadraticBracket (baseMap u) (e 0) := by
    rw [conjugate,conjugate_second]
    simp [conjugator,generator,quadraticBracket]
    rfl
  rw [h,quadraticBracket_comm,secondDetector_bracket_baseMap]

/-- The six central conjugator parameters are detected independently in degree three. -/
theorem quadratic_conjugate_third_detect (v : U) :
    thirdDetector (quadraticWord v*generator 0*(quadraticWord v)⁻¹).third=v := by
  rw [conjugate_of_first_zero _ _ (quadraticWord_first v)]
  change thirdDetector (0-bracket (e 0) (quadraticWord v).second)=v
  rw [zero_sub,map_neg,quadraticWord_second,thirdDetector_bracket_selectedMap]
  ext i
  exact ZMod.neg_eq_self_mod_two _

/-- Actual conjugacy in the concrete cut quotient has at least twelve independent bits. -/
theorem conjugate_injective (tails : Fin 16 → V₃ F) :
    Function.Injective (fun p : U × U => quotientMap tails (conjugate p.1 p.2)) := by
  intro p q hpq
  have hu : p.1=q.1 := by
    have h := secondDetector_eq_of_quotient tails (conjugate p.1 p.2) (conjugate q.1 q.2)
      (by simp [conjugate]) hpq
    simpa only [conjugate_second_detect] using h
  have hv : p.2=q.2 := by
    have hq : quotientMap tails
        (quadraticWord p.2*generator 0*(quadraticWord p.2)⁻¹)=
      quotientMap tails (quadraticWord q.2*generator 0*(quadraticWord q.2)⁻¹) := by
      have h := congrArg (fun x : Cut tails =>
        (quotientMap tails (baseWord q.1))⁻¹*x*quotientMap tails (baseWord q.1)) hpq
      simpa [conjugate,conjugator,hu,map_mul,map_inv,mul_assoc] using h
    have h := thirdDetector_eq_of_quotient tails
      (quadraticWord p.2*generator 0*(quadraticWord p.2)⁻¹)
      (quadraticWord q.2*generator 0*(quadraticWord q.2)⁻¹)
      (by simp)
      (by rw [conjugate_of_first_zero _ _ (quadraticWord_first p.2),
        conjugate_of_first_zero _ _ (quadraticWord_first q.2)]) hq
    simpa only [quadratic_conjugate_third_detect] using h
  exact Prod.ext hu hv

end Certificate
end UnitDistance.TruncatedMagnus
