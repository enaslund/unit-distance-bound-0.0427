module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! The finite abelian groups imposed at the five odd ramified primes,
with their universal mapping property for arbitrary ambient groups. -/
noncomputable section
namespace UnitDistance.OddLocal

abbrev Cyclic (n : ℕ) := Multiplicative (ZMod n)
def cyclicGenerator (n : ℕ) : Cyclic n := Multiplicative.ofAdd 1

def cyclicMap {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g^n=1) : Cyclic n →* G :=
  (ZMod.lift n ⟨{
    toFun := fun k : ℤ ↦ Additive.ofMul (g^k)
    map_zero' := by simp
    map_add' := fun k l ↦ by change g^(k+l)=g^k*g^l; rw [zpow_add]},by
      change g^(n : ℤ)=1
      simpa using hg⟩).toMultiplicativeLeft

theorem cyclicMap_cast {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g^n=1) (k : ℤ) :
    cyclicMap n g hg (Multiplicative.ofAdd (k : ZMod n))=g^k := by
  exact congrArg Additive.toMul (ZMod.lift_coe n _ k)

@[simp] theorem cyclicMap_generator {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g^n=1) :
    cyclicMap n g hg (cyclicGenerator n)=g := by
  simpa [cyclicGenerator] using cyclicMap_cast n g hg 1

theorem cyclic_eq_generator_zpow (n : ℕ) (x : Cyclic n) :
    ∃ k : ℤ, x=cyclicGenerator n^k := by
  obtain ⟨k,hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k,?_⟩
  apply Multiplicative.toAdd.injective
  simpa [cyclicGenerator] using hk.symm

theorem cyclicMap_mem_zpowers {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g^n=1)
    (x : Cyclic n) : cyclicMap n g hg x∈Subgroup.zpowers g := by
  obtain ⟨k,rfl⟩ := cyclic_eq_generator_zpow n x
  simp only [map_zpow,cyclicMap_generator]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) k

def residueDegree (i : Fin 5) : ℕ := if i.val<2 then 2 else 4
instance residueDegree_neZero (i : Fin 5) : NeZero (residueDegree i) := by
  refine ⟨?_⟩
  simp only [residueDegree]
  split <;> omega

abbrev D (i : Fin 5) := Cyclic 2 × Cyclic (residueDegree i)
def inertia (i : Fin 5) : D i := (cyclicGenerator 2,1)
def frobenius (i : Fin 5) : D i := (1,cyclicGenerator (residueDegree i))

theorem card (i : Fin 5) : Nat.card (D i)=2*residueDegree i := by
  simp only [D,Nat.card_eq_fintype_card,Fintype.card_prod,Cyclic,Fintype.card_multiplicative,ZMod.card]

theorem normal_form (i : Fin 5) (g : D i) :
    ∃ a b : ℤ, g=inertia i^a*frobenius i^b := by
  obtain ⟨a,ha⟩ := cyclic_eq_generator_zpow 2 g.1
  obtain ⟨b,hb⟩ := cyclic_eq_generator_zpow (residueDegree i) g.2
  exact ⟨a,b,by ext <;> simp [inertia,frobenius,ha,hb]⟩

theorem generators (i : Fin 5) : Subgroup.closure ({inertia i,frobenius i} : Set (D i))=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a,b,rfl⟩ := normal_form i g
  exact Subgroup.mul_mem _
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) a)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) b)

theorem hom_ext {G : Type*} [Group G] (i : Fin 5) (f g : D i →* G)
    (ht : f (inertia i)=g (inertia i)) (hf : f (frobenius i)=g (frobenius i)) : f=g := by
  ext x
  obtain ⟨a,b,rfl⟩ := normal_form i x
  simp only [map_mul,map_zpow,ht,hf]

def map {G : Type*} [Group G] (i : Fin 5) (t f : G)
    (ht : t^2=1) (hf : f^residueDegree i=1) (hc : Commute t f) : D i →* G :=
  (cyclicMap 2 t ht).noncommCoprod (cyclicMap (residueDegree i) f hf) (by
    intro x y
    obtain ⟨a,rfl⟩ := cyclic_eq_generator_zpow 2 x
    obtain ⟨b,rfl⟩ := cyclic_eq_generator_zpow (residueDegree i) y
    simp only [map_zpow,cyclicMap_generator]
    exact (hc.zpow_left a).zpow_right b)

@[simp] theorem map_inertia {G : Type*} [Group G] (i : Fin 5) (t f : G)
    (ht : t^2=1) (hf : f^residueDegree i=1) (hc : Commute t f) :
    map i t f ht hf hc (inertia i)=t := by
  simp [map,inertia]

@[simp] theorem map_frobenius {G : Type*} [Group G] (i : Fin 5) (t f : G)
    (ht : t^2=1) (hf : f^residueDegree i=1) (hc : Commute t f) :
    map i t f ht hf hc (frobenius i)=f := by
  simp [map,frobenius]

end UnitDistance.OddLocal
