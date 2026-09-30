module

public import UnitDistance.GroupAugmentationFoxCharacters
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section
set_option backward.privateInPublic true


/-! First moments of actual group-algebra elements along binary characters. -/
noncomputable section
namespace UnitDistance.GroupAugmentation
variable {G : Type*} [Group G]
abbrev Binary := ZMod 2

def moment (χ : G →* Multiplicative Binary) : A Binary G →ₗ[Binary] Binary :=
  (Finsupp.linearCombination Binary (fun g => (χ g).toAdd)).comp
    (MonoidAlgebra.coeffLinearEquiv Binary).toLinearMap

@[simp] theorem moment_delta (χ : G →* Multiplicative Binary) (g : G) :
    moment χ (delta Binary g)=(χ g).toAdd := by simp [moment,delta]
@[simp] theorem moment_one (χ : G →* Multiplicative Binary) : moment χ 1=0 := by
  rw [←delta_one Binary,moment_delta,map_one]
  rfl

/-- The character moment satisfies the actual augmentation product rule. -/
theorem moment_mul (χ : G →* Multiplicative Binary) (a b : A Binary G) :
    moment χ (a*b)=augmentation Binary G a*moment χ b+
      augmentation Binary G b*moment χ a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul,map_add,ha,ha',mul_add]; ring
  | single g c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add,map_add,hb,hb',add_mul]; ring
    | single h d =>
      have hg : MonoidAlgebra.single g c=c • delta Binary g := by simp [delta]
      have hh : MonoidAlgebra.single h d=d • delta Binary h := by simp [delta]
      rw [hg,hh,smul_mul_smul,delta_mul]
      simp only [map_smul,moment_delta,augmentation_delta,smul_eq_mul,mul_one,map_mul]
      change (c*d)*((χ g).toAdd+(χ h).toAdd)=c*(d*(χ h).toAdd)+d*(c*(χ g).toAdd)
      ring

/-- Every second augmentation power has zero scalar and character moments. -/
theorem moment_power_two (χ : G →* Multiplicative Binary) (a : A Binary G)
    (ha : a∈power Binary G 2) : moment χ a=0 := by
  induction ha using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a,ha,b,hb,rfl⟩ := hv
    rw [power_one] at ha
    change augmentation Binary G a=0 at ha
    rw [moment_mul,ha,hb,zero_mul,zero_mul,zero_add]
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

end UnitDistance.GroupAugmentation
