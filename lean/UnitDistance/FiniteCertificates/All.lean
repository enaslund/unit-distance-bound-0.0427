module

public import UnitDistance.FiniteCertificates.Prime2
public import UnitDistance.FiniteCertificates.Prime3
public import UnitDistance.FiniteCertificates.Prime5
public import UnitDistance.FiniteCertificates.Prime7
public import UnitDistance.FiniteCertificates.Prime11
public import UnitDistance.FiniteCertificates.Prime13
public import UnitDistance.FiniteCertificates.Prime17
public import UnitDistance.FiniteCertificates.Prime19
public import UnitDistance.FiniteCertificates.Prime23
public import UnitDistance.FiniteCertificates.Prime29
public import UnitDistance.FiniteCertificates.Prime31

@[expose] public section
set_option backward.privateInPublic true


/-! # Assembly of individually proved finite-place enclosures

The entries below are untrusted rational candidates. The theorems connect
all entries to the actual witness and to the separately proved inequalities.
-/
noncomputable section
namespace UnitDistance.Witness.FiniteCertificates

def residueLogUpper : Fin 11 → ℝ :=
  ![(2772588722239781239 : ℝ) / 1000000000000000000, (274653072167027423 : ℝ) / 125000000000000000, (12875503299472803 : ℝ) / 4000000000000000, (3891820298110626611 : ℝ) / 500000000000000000, (9591581091193482177 : ℝ) / 1000000000000000000, (2051959485969229389 : ℝ) / 200000000000000000, (5666426688112432161 : ℝ) / 500000000000000000, (11777755916665761841 : ℝ) / 1000000000000000000, (2508395372743319753 : ℝ) / 200000000000000000, (1346918331994589611 : ℝ) / 100000000000000000, (2747189763588116997 : ℝ) / 200000000000000000]

def energyLogLower : Fin 11 → ℝ :=
  ![(1100514558076640253 : ℝ) / 500000000000000000, (2518205691434532483 : ℝ) / 1000000000000000000, (504523225214088207 : ℝ) / 250000000000000000, (219842256085367339 : ℝ) / 200000000000000000, (549330360630729517 : ℝ) / 500000000000000000, (693220116235512857 : ℝ) / 1000000000000000000, (693164289110647631 : ℝ) / 1000000000000000000, (34657838237794773 : ℝ) / 50000000000000000, (693150802830320077 : ℝ) / 1000000000000000000, (138629665372493509 : ℝ) / 200000000000000000, (173287001387715051 : ℝ) / 250000000000000000]

def massLogUpper : Fin 11 → ℝ :=
  ![(26929560148739163 : ℝ) / 500000000000000000, (4849925787637543 : ℝ) / 50000000000000000, (15738079286089629 : ℝ) / 500000000000000000, (113237443587377 : ℝ) / 500000000000000000, (16860527674513 : ℝ) / 1000000000000000000, (26591143070619 : ℝ) / 1000000000000000000, (5966562545843 : ℝ) / 1000000000000000000, (3287442227291 : ℝ) / 1000000000000000000, (605239509657 : ℝ) / 500000000000000000, (372581251753 : ℝ) / 1000000000000000000, (66459335913 : ℝ) / 250000000000000000]

theorem power_bounds (v : Fin 11) (i : Fin 6) :
    (shellWeights v i : ℝ) ^ p ≤ powerUpper v i := by
  fin_cases v <;> fin_cases i
  · exact power_bound_0_0
  · exact power_bound_0_1
  · exact power_bound_0_2
  · exact power_bound_0_3
  · exact power_bound_0_4
  · exact power_bound_0_5
  · exact power_bound_1_0
  · exact power_bound_1_1
  · exact power_bound_1_2
  · exact power_bound_1_3
  · exact power_bound_1_4
  · exact power_bound_1_5
  · exact power_bound_2_0
  · exact power_bound_2_1
  · exact power_bound_2_2
  · exact power_bound_2_3
  · exact power_bound_2_4
  · exact power_bound_2_5
  · exact power_bound_3_0
  · exact power_bound_3_1
  · exact power_bound_3_2
  · exact power_bound_3_3
  · exact power_bound_3_4
  · exact power_bound_3_5
  · exact power_bound_4_0
  · exact power_bound_4_1
  · exact power_bound_4_2
  · exact power_bound_4_3
  · exact power_bound_4_4
  · exact power_bound_4_5
  · exact power_bound_5_0
  · exact power_bound_5_1
  · exact power_bound_5_2
  · exact power_bound_5_3
  · exact power_bound_5_4
  · exact power_bound_5_5
  · exact power_bound_6_0
  · exact power_bound_6_1
  · exact power_bound_6_2
  · exact power_bound_6_3
  · exact power_bound_6_4
  · exact power_bound_6_5
  · exact power_bound_7_0
  · exact power_bound_7_1
  · exact power_bound_7_2
  · exact power_bound_7_3
  · exact power_bound_7_4
  · exact power_bound_7_5
  · exact power_bound_8_0
  · exact power_bound_8_1
  · exact power_bound_8_2
  · exact power_bound_8_3
  · exact power_bound_8_4
  · exact power_bound_8_5
  · exact power_bound_9_0
  · exact power_bound_9_1
  · exact power_bound_9_2
  · exact power_bound_9_3
  · exact power_bound_9_4
  · exact power_bound_9_5
  · exact power_bound_10_0
  · exact power_bound_10_1
  · exact power_bound_10_2
  · exact power_bound_10_3
  · exact power_bound_10_4
  · exact power_bound_10_5

theorem residue_log_upper (v : Fin 11) : Real.log (residueCard v) ≤ residueLogUpper v := by
  fin_cases v
  · have h := residue_log_0.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_1.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_2.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_3.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_4.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_5.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_6.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_7.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_8.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_9.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h
  · have h := residue_log_10.2
    norm_num [residueLogUpper, residueCard, primes, residueDegree, Matrix.cons_val] at h ⊢
    exact h

theorem energy_log_lower (v : Fin 11) : energyLogLower v ≤ Real.log (energyLower v) := by
  fin_cases v
  · have h := energy_log_0.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_1.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_2.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_3.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_4.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_5.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_6.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_7.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_8.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_9.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h
  · have h := energy_log_10.1
    norm_num [energyLogLower, energyLower, Matrix.cons_val] at h ⊢
    exact h

theorem mass_log_upper (v : Fin 11) : Real.log (massUpper v) ≤ massLogUpper v := by
  fin_cases v
  · have h := mass_log_0.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_1.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_2.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_3.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_4.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_5.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_6.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_7.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_8.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_9.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h
  · have h := mass_log_10.2
    norm_num [massLogUpper, massUpper, Matrix.cons_val] at h ⊢
    exact h

end UnitDistance.Witness.FiniteCertificates
