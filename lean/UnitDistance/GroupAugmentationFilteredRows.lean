module

public import UnitDistance.GroupAugmentationProductBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Strict induction of actual local coefficient rows

Under an actual filtered right-module decomposition, a strict local row
induces a strict ambient image filtration. Kernel vectors need not have
the degree of their image: the proof chooses a suitable local representative
in each actual coordinate block and reconstructs an ambient representative.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G] {ι : Type*}

/-- An actual coefficient row acts by right multiplication. -/
def coefficientRow (c : ι → A R G) : A R G →ₗ[R] (ι → A R G) where
  toFun a i := a*c i
  map_add' a b := by funext i; exact add_mul ..
  map_smul' r a := by funext i; exact smul_mul_assoc ..

/-- The row image of actual degree-`n` coefficients. -/
def rowImagePower (c : ι → A R G) (n : ℕ) : Submodule R (ι → A R G) :=
  (power R G n).map (coefficientRow R G c)

variable (D P T : Type*) [Group D] [Group P] [Fintype T] (f : D →* P)
variable (e : A R P ≃ₗ[R] (T →₀ A R D)) (w : T → ℕ)
variable (hmul : ∀ a b t, e (a*induced R D f b) t = e a t*b)
variable (hpower : ∀ a n, a ∈ power R P n ↔ ∀ t, e a t ∈ power R D (n-w t))

omit [Group G] in
/-- Local image strictness is equivalently the ability to choose an actual
preimage of the specified degree, allowing for the true row kernel. -/
theorem row_lift_of_image_strict (c : ι → A R D)
    (hlocal : ∀ n, rowImagePower R D c n =
      (coefficientRow R D c).range ⊓ coefficientPower R D (ι := ι) (n+1))
    (n : ℕ) (a : A R D) (ha : ∀ i, a*c i ∈ power R D (n+1)) :
    ∃ b ∈ power R D n, ∀ i, b*c i = a*c i := by
  have hi : coefficientRow R D c a ∈ rowImagePower R D c n := by
    rw [hlocal]
    exact ⟨⟨a,rfl⟩,(mem_coefficientPower R D _ _).mpr ha⟩
  obtain ⟨b,hb,he⟩ := hi
  exact ⟨b,hb,fun i => congrFun he i⟩

omit [Group G] in
include hmul hpower in
/-- An actual ambient row with the required coefficient degree has an
actual ambient preimage of the required degree. -/
theorem induced_row_lift (c : ι → A R D)
    (hlocal : ∀ n (a : A R D), (∀ i, a*c i ∈ power R D (n+1)) →
      ∃ b ∈ power R D n, ∀ i, b*c i = a*c i)
    (n : ℕ) (a : A R P) (ha : ∀ i, a*induced R D f (c i) ∈ power R P (n+1)) :
    ∃ b ∈ power R P n, ∀ i, b*induced R D f (c i) = a*induced R D f (c i) := by
  classical
  have hchoose : ∀ t, ∃ b ∈ power R D (n-w t), ∀ i, b*c i = e a t*c i := by
    intro t
    by_cases ht : n < w t
    · refine ⟨e a t,?_,fun _ => rfl⟩
      rw [Nat.sub_eq_zero_of_le (by omega : n ≤ w t),power_zero]
      trivial
    · apply hlocal (n-w t) (e a t)
      intro i
      have hi := (hpower _ (n+1)).mp (ha i) t
      rw [hmul] at hi
      have he : (n+1)-w t = (n-w t)+1 := by omega
      rwa [he] at hi
  choose b hb he using hchoose
  let b' : T →₀ A R D := Finsupp.equivFunOnFinite.symm b
  let a' : A R P := e.symm b'
  have ha' : ∀ t, e a' t = b t := by intro t; simp [a',b']
  refine ⟨a',(hpower a' n).mpr (fun t => (ha' t).symm ▸ hb t),?_⟩
  intro i
  apply e.injective
  apply Finsupp.ext
  intro t
  rw [hmul,hmul,ha']
  exact he t i

omit [Group G] in
include hmul hpower in
/-- The induced row image has exactly the filtration inherited from the
actual ambient coefficient space, shifted by one coefficient degree. -/
theorem induced_rowImagePower_eq_induced (c : ι → A R D)
    (hc : ∀ i, c i ∈ power R D 1)
    (hlocal : ∀ n, rowImagePower R D c n =
      (coefficientRow R D c).range ⊓ coefficientPower R D (ι := ι) (n+1)) (n : ℕ) :
    rowImagePower R P (fun i => induced R D f (c i)) n =
      (coefficientRow R P (fun i => induced R D f (c i))).range ⊓
        coefficientPower R P (ι := ι) (n+1) := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨⟨a,rfl⟩,(mem_coefficientPower R P _ _).mpr ?_⟩
    intro i
    apply mul_mem_add R P ha
    exact induced_mem_power R D f 1 (c i) (hc i)
  · rintro ⟨⟨a,rfl⟩,ha⟩
    obtain ⟨b,hb,he⟩ := induced_row_lift R D P T f e w hmul hpower c
      (row_lift_of_image_strict R D c hlocal) n a ((mem_coefficientPower R P _ _).mp ha)
    exact ⟨b,hb,funext he⟩

end UnitDistance.GroupAugmentation
