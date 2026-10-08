> Fresh-context readability review of the revision of October 8, 2026 (branch paper-readability at ea86e96e), by an AI agent given only the sources and the brief; read-only. Its findings were applied in commits e790e6d9, e9f75425, 7fb63e20 and 1e62b84c. Paths under /tmp refer to the reviewer's scratch space and are not part of the repository.

# Review of the readability revision of papers/0.043171 (branch paper-readability vs master)

**Scope.** The diff reviewed is `git diff master...paper-readability -- papers/0.043171/sections papers/0.043171/main.tex`. It touches 15 files, with about 3200 lines inserted and 1500 deleted. The review was read-only: nothing in the repository was edited or committed. `make` was run once, and the tree was then restored (see E).

**Line numbers** refer to the files on branch paper-readability (head ea86e96e) unless "old" is said.

**How the work was split.** The files went to six fresh readers:
- tower;
- genus-field and analytic;
- dihedral;
- lvalues and ceiling;
- geometry and finite-windows;
- profiles, certificate, limits, finite-witness and main.tex.

I checked the introduction, Figure 1, the dependency index and the build myself. I re-verified the readers' most consequential findings; these are marked [verified].

---

## Summary

1. **No mathematics was changed.**
   - I compared the multiset of all numerals in each file, old against new, with comments, labels and citations stripped. Every file shows only additions; no number was removed or altered.
   - Each change the readers found to a formula, constant, hypothesis or claim is one of three things: a renaming, a restatement of old prose as a numbered statement, or a new and correct justification of an old claim.
   - One hypothesis was narrowed, harmlessly: Proposition lim:B. It is not used for Theorem 1.1 (A.3).
   - Renamings are consistent. No old symbol from the brief survives. There are two exceptions:
     - an inconsistency left behind: M_R versus M_fin (A.4);
     - a new notation overlap: f^0_p, which now means both the floor and the lower bound of Proposition an:prime-budget (B.1).
2. **Terms used before definition.**
   - Mostly solved in the body sections.
   - Section 1.3 ("The structure of the proof") and Figure 1 come before Section 1.4. Together with line 157 of Section 1.2, they use G_B, D_4G_B, floors, free primes, E_{W''}, σ_j and C_eff before the introduction defines them or refers to them.
3. **Statements.** No new numbered statement is false. A few have small problems: incomplete or implicit hypotheses, wrong "used in" claims, and one ambiguous sentence (C).
4. **Figure 1 is not accurate as captioned.**
   - It is a transitive reduction, which the caption does not say. 27 "uses" pairs between shown statements are not drawn, 10 of them direct citations.
   - Three arrows come from pointer citations, not uses. One of them, fw:transfer → cert:places, hides the real arrow fw:transfer → thm:main.
   - Three arrows pass through other boxes.
   - The claim that "the four parts meet only in the final inequality" is contradicted by the figure's own cross-part arrows.
5. **The dependency index is a faithful listing of `\ref`, but `\ref` is an imperfect proxy for "uses".**
   - About 31 uses are cited only through `\eqref` of an equation inside another statement, and the index drops them.
   - Several statements are used without any `\ref`.
   - Several `\ref` are pointers, not uses.
   - So "lists the complete graph" overstates (D).
6. **Build: clean.**
   - No errors, no undefined references or citations, no multiply-defined labels, no overfull boxes.
   - 99 pages (master: 83).
   - The rebuilt PDF is textually identical to the committed one.
   - `tools/depgraph.py --check` passes.

---

## A. Unintended changes

### A.1 Method

- **Numbers.** I extracted all numerals from old and new versions of each file and compared them as multisets, after stripping comments and `\ref/\label/\cite/\path/\texttt` arguments.
  - Result: in every one of the 15 files the "lost" set is empty.
  - So no number was replaced. A change X→Y would show X as lost unless X was added elsewhere in the same file, and the readers found no such case in the hunk-by-hunk pass.
  - New numbers only accompany new text: openers, restated statements, and new justifications.
- **Hunks.** Each reader went through its files hunk by hunk.

### A.2 Substantive changes and verdicts

All of the following are equivalent to the old text, or correct new arguments for old claims.

| File:line | Change | Verdict |
|---|---|---|
| introduction.tex:155-159 | "ι_1, which is far from central" becomes "whose conjugacy class in G_B/D_4G_B has 2^15 elements (Lemma tw:retained-quotient(c)), which forces b/d ≤ 2^-16 and θ ≥ θ_*" | Correct, more specific. It matches tower.tex:1068, 1721-1723; (1-2^-16)/2 = 65535/131072. [verified] |
| introduction.tex:117-119 | New: rd(K) "equals that of F because K/F will be unramified at the finite places" | Correct; see an:family (analytic.tex:31-32) and tower.tex:1752. [verified] |
| introduction.tex:208 | "a fourth power lies in that term" becomes "every fourth power lies in D_4G_B" | Equivalent (g^4 ∈ D_4 in the 2-Zassenhaus filtration) |
| introduction.tex:251-257 | New citation [TV, Prop. 3.1]; w(q) = 2 log q Σ(q^m+1)^-1 and g_σ written out | Match analytic.tex:244 and 285. [verified] |
| introduction.tex:265-270 | Shells defined: S_0 = O, S_i the elements of valuation -i | Matches finite-windows.tex:107 (S_i = B_i \ B_{i-1}). [verified] |
| tower.tex:84 | Theorem tw:jennings in the "any fixed order" form | Equivalent (relabelling) |
| tower.tex (tw:vectors, tw:beta, tw:graded) | Prose became lemmas; tw:graded now proved; tw:beta adds "unique" | Correct (reader recomputed the vector rows) |
| tower.tex:581-585 | New: the elementary image of Frob_ν is independent of the place | Correct (Gal(E/B) abelian) |
| genus-field.tex:93-95 | Frobenius vector of t_4 is 00110100 | Matches tower.tex:619 |
| genus-field.tex:131-133 | Conductor formula moved into Prop gf:local-data(5) | Equivalent |
| analytic.tex:332-335 | New: Y'_* bounds -[K:Q]^-1 ζ'_K/ζ_K(2) | Correct, but it sits between statement and proof (move it after the proof) |
| analytic.tex:375-380, 392-408 | β^sel_q with e_K f_K; values moved into an:selected-lemma | Equivalent; Z_sel(1) ≈ 0.0416684840 recomputed |
| analytic.tex:860-890 | New Lemma an:afe-range with a proof. Old text only said "between 49.0 and 50.6" | Correct. I recomputed tN ≤ 50.4992 < 50.6, 2π(8-6/√723) = 48.863, t ≥ 0.003373 > 0.0033, and t(N+1) = 49.0716 at Q=723 and 50.5919 at Q=964. The reader counted 53 conductor values. [verified] |
| analytic.tex:1056-1079 | Remark an:base-ceiling now gives Y_* = Y_E - Δ^E_sel - Δ^E_4 | Consistent with papers/0.042901/certificates/ceiling41.py |
| dihedral.tex:86-100 | New Lemma dh:dihedral-polar (was prose); adds "radical = ker φ" | Correct; the old proof of dh:EW(c) already used it |
| dihedral.tex:154-159 | dh:detection(d): Frobenius elements lie in D_2G_B and share one class in gr_2 | Was in the old proof and in the old definition of c_p |
| dihedral.tex:234-259, 369-396, 786-806 | New Lemmas dh:beta-exists, dh:vector-zero, dh:inert-v0 (were prose); "norm ≤ 1.2e7" written as "p² ≤ 1.2e7" for inert primes | Equivalent. p ≡ 1, 49 (mod 120) was re-derived |
| dihedral.tex:295-316 | Definition dh:W now also contains W, W' (moved from limits.tex) and "lies in ker W''" (moved from dh:census) | W = ⟨ψ10, ψ23⟩, W' = ⟨ψ10, ψ23, ψ19⟩, as in the old limits.tex |
| dihedral.tex:351-367 | Definition dh:census-basis gives the order (0,5,9,17,22,14,3,7,4,15,6,20,12,24,13) explicitly | Matches certificates/d4fields15.json |
| dihedral.tex:398-440 | dh:pattern-lemma(b), (e): explicit decompositions with the bit convention | Checked against wmasks4.json and the d4fields.py rank assert |
| dihedral.tex:617-628 | New Remark dh:EW-sub (subspaces U ⊆ W'') | Consistent with the old limits.tex figures (2048, 192, 4096, 32) |
| dihedral.tex:874-902 | New Lemma dh:delta-sel, an explicit formula for old prose | Re-derived; matches dihedral_ceiling3.py:172-191 |
| lvalues.tex:164-190 | New Lemma lv:remainders (Taylor remainder, Rankin tail). Adds the hypothesis 0 < s_0 | Equivalent in every use (s_0 > 1) |
| lvalues.tex:225-283 | New Lemma lv:coefficients from the old prose rules ("a_p = 0 if p inert", "q ≠ 241") | Equivalent |
| lvalues.tex:15-23 | Citations to [0418235, §4.6, Lemma 4.4; §4.7; §4.9] | Checked against that paper |
| ceiling.tex:114-128 | Renames: C → P_2, E(σ) → Y_cor, τ → T_c | Same sets and quantities |
| geometry.tex | New lemmas geo:norm-one (now proved), geo:prime-count, geo:exponents, geo:phi-omega(b) (new continuity proof), geo:counts | Correct; the reader re-derived e^{dH}, e^{dJ} and continuity |
| finite-windows.tex:39 | fw:shift-operator now restricted to locally constant, compactly supported g | Every use is of that kind |
| finite-windows.tex:435 | fw:rescaling: Remark → Lemma with proof; n_p ∈ Z made explicit | Correct |
| certificate.tex:53-56, 73-87 | "Index 41 always means t_3"; new Def cert:effective-types | Correct; content was in the old proof of cert:places |
| certificate.tex:313-315 | "It is the margin (fw:margin)" moved from the proof of thm:main into the statement of cert:lower-margin | Equivalent |
| limits.tex:91-96 | New: R_p(f) ≥ 0 and "the sum of the credits is at least G_p" | Correct (monotonicity in an:local-contribution; ρ_K = 0 for odd f) |
| limits.tex:271-275 | New C' = 0.04871285, σ = 301/300, X = 1.2·10^7 for the 1.042925 step | Matches certificates/witness_0.042925.json |
| main.tex (abstract) | "low Zassenhaus quotients" becomes "its quotient by the fourth Zassenhaus term"; "profit of that condition" becomes "contribution of the capped prime to the margin" | Equivalent, more precise |

### A.3 Not strictly equivalent

**limits.tex:182-198, Proposition lim:B (Adaptive margin): the hypotheses were narrowed.**
- **Old:** "Take shell profiles at the places above the selected primes … with the H_f of these places, and let M_* be the lower bound for their margin, as in Definition cert:lower-bounds, computed with C'."
- **New:** "Let P and R be as in Definition cert:data(e) … g_r a shell profile with parameters (Q_r,k_r,w^(r)) … H_f = H, the number H of Lemma cert:places. Let J_C^* ≤ J_C …".
- **Effect:** Q_r and k_r are now fixed to those of Table cert:tab-local, and only the weights may vary.
- **Why it is harmless:** every witness of an intermediate step uses k = {2:7, 3:9, 5:6, 29:1, 41:1}, the same as the table (reader checked the JSON). lim:B is not used for Theorem 1.1.
- **Suggested fix:** either "with Q_r, k_r of Table cert:tab-local" stated openly, or allow any k_r with H = Σ_r k_r log r / e_r.

### A.4 Renaming consistency

- **No survivors of the brief's old symbols.** None of the following remains in any section:
  - kernel λ (λ now only means the root discriminant; geometry.tex:559 is the root discriminant);
  - floor sum F(σ);
  - D_4 as a group (every D_4 is D_4G_B or similar);
  - f_p for floors; b for b_TV; Z(g); σ as the Fourier constant (now ς everywhere: certificate.tex:233, 301-302; profiles.tex:306-396);
  - (F1)/(F2) as floor conditions.
- **The dyadic group** D → \mathcal D is consistent, with N_D, s_D, ψ_D, Λ_D, I_D and Ω_D renamed to match.
- **tower.tex:1223-1407 (F1)-(F4)** are the Fox-calculus properties of Lemma tw:row-properties. This is intended; the floor conditions became (Fl1)/(Fl2) to avoid the clash.
- **Other renamings, all applied consistently in their files:**
  - \mathcal F → \mathfrak F; F^n → Fil^m; χ_a → κ_a;
  - I_N → u_N; κ → h_cap; h(M) → h_Her; I → \mathfrak b; ν(u) → \mathbf e(u);
  - L → \mathsf L; Δ, \mathcal G → \mathbf D, \mathbf G; Γ → \mathcal O_P;
  - \mathcal D → Y'_*; q → q_⋆;
  - \mathcal B_i → Bin_i; S_{1,2} → S^{(1,2)}; N_e → N^afe_e.
- **Left inconsistent.** certificate.tex now calls the margin \mathcal M_fin(θ) (lines 312, 317, 328-329, 362-364; old \mathcal M_R). Two problems follow:
  - The same formula in Corollary fw:uniform-types is still \mathcal M_R(θ) (finite-windows.tex:764, 770, 775).
  - \mathcal M_fin already denotes a single margin in the proof of fw:transfer (finite-windows.tex:567).
  - **Fix:** use one name, for example M_R in both, or rename the fw:transfer-proof symbol.
- **κ has two meanings.** κ_a/κ_b, the Kummer characters (genus-field.tex:53, tower.tex:335; new names for χ_a), sit beside κ_∞, which the notation table lists among symbols "that keep one meaning throughout" (introduction.tex:361, 387).
  - **Fix:** use another letter for the characters, or qualify the table.

---

## B. Terms used before definition, and symbols with two meanings

### B.1 Notation introduced or exposed by the revision

1. **f^0_p has two meanings in Section 4.**
   - Proposition an:prime-budget (analytic.tex:315-321) uses e^0_p, f^0_p for arbitrary lower bounds of e_K and f_K at every prime of B. Remark an:base-ceiling (:1060) uses it in that sense, including at selected primes.
   - Definition an:floor-def (:420-427) uses f^0_p for the floor, a divisor of f_K defined only for free primes. This is the revision's new name for the old f_p.
   - The notation table (introduction.tex:391) gives only the floor meaning.
   - **Fix:** rename the prime-budget bounds (e^-_p, f^-_p), or say at an:floor-def that a system of floors is an admissible choice of f^0 in Proposition an:prime-budget.
2. **K, \mathcal K and \mathsf K together.** In Proposition an:signed and its proof (analytic.tex:456-525), "write K = K^(j)" sits next to \mathsf K(Np^f). The glyphs differ, but the passage is hard to read.
   - **Fix:** use a different letter for the kernel (for example \mathsf k or Φ).
3. **lvalues.tex:150-156 vs :226-245.** The grid points c_0 > c_1 > … (c_0 = 6144) sit in the same subsection as the index o in B_{c_o}; c_0 and c_o look identical.
   - The moments M_ij (:194-201) sit beside the fields M_o and M_{o,w}. The old text had K_w, so this clash is new.
   - **Fix:** rename the grid points (ξ_i) and the moments (S_ij).
4. **lvalues.tex:240-247.** The index o is unbound in Lemma lv:coefficients(b).
   - **Fix:** add "for o ∈ {a, b}".
5. **finite-windows.tex:333, 668-675.** In \mathfrak a_{\mathcal C}, P_{\mathcal C} and \mathcal C', the subscript \mathcal C is the period of one shell profile (lines 128 and 141), but the group meant is \mathcal C_f.
   - **Fix:** write \mathfrak a_{\mathcal C_f}.
6. **geometry.tex:823, 856.** The ideal \mathfrak b (renamed from I) appears next to the signature b ("b/d = 1-2θ") in the proof of geo:transfer.
   - **Fix:** use another letter, or add a note.
7. **tower.tex:1168-1170.** The new convention "n denotes the rank, filtration indices are written m" is broken in two places in the same subsection:
   - (F4) at :1227 ("free on f'_1,…,f'_m");
   - Lemma tw:filtered-local-freeness at :1303 and :1319, where n is a degree in the hypothesis and the rank in (c).
   - **Fix:** write "injective on gr_1 and gr_2", and use f'_1..f'_r.
8. **lvalues.tex:122.** ϖ is a convolution density, while elsewhere ϖ is a uniformizer. Minor.

### B.2 Introduction, read in order

Each item gives the line, the problem and a suggested fix.

1. **:157.** "whose conjugacy class in $G_B/D_4G_B$ has $2^{15}$ elements".
   - G_B and D_4G_B are used here, but are defined only at :205-207 (Section 1.4), which also says "(recalled at the start of Section 2)".
   - **Fix:** move the definition ("the tower group G_B (Definition tw:GB) and the fourth term D_4G_B of its Zassenhaus filtration") to :150-157, and shorten :205-207.
2. **:130.** "selected primes of fixed local types". "Local type" is not defined or referenced.
   - **Fix:** add "(Definition tw:type)".
3. **:170.** "the graded pieces of its Zassenhaus filtration" are not yet defined; that happens at :207 and :220.
   - **Fix:** add a reference to the start of Section 2.
4. **:174-177, Part (II).** Uses "signed kernel", "real points σ_j", "ζ_{E_{W''}}", "the floors of the free primes" and "the census" with no definition or reference. They are defined at :233-235 and :253, or only in the body (Definitions an:selected-def, an:floor-def and dh:W, Proposition dh:census).
   - **Fix:** add these references in (II).
5. **:189, Part (IV).** "with C = C_eff from (II)". C_eff is defined at :260.
   - **Fix:** add "(Theorem an:ceiling)".
6. **Figure 1 (page 4).** It uses G_B, gr_2, G_B/D_4G_B, E_{W''} and C_eff, and is placed before Section 1.4.
   - **Fix:** add to the caption "Notation: Subsection 1.7", or place the figure after Section 1.4.
7. **:245-246 vs :252-254.** "kernels" in (c) are the cut-off functions of the approximate functional equation; in (d) the kernel is \mathsf K.
   - **Fix:** in (c), write "whose cut-off functions (kernels) are certified".
8. **Notation table.** Five entries need correcting:
   - **:387 (κ_∞):** "the Tsfasman–Vlăduţ weight and right side". In fact 2κ_∞ is the right side (analytic.tex:246, 262). **Fix:** "w(q), the Tsfasman–Vlăduţ weight; 2κ_∞, the right side of the inequality".
   - **:393 (ψ_o):** cites Definition dh:dihedral-type, but the numbering ψ_o, o = 0..26, is introduced in the proof of Lemma dh:27 (dihedral.tex:115). **Fix:** cite Lemma dh:27.
   - **:379 (B_G):** "B_G … its fixed field (Gal(B_G/B) = G_B)". B_G is the fixed field of N in B_S, that is the field of the tower, not "the fixed field of G_B" (which would be B). **Fix:** "the tower field B_G ⊂ B_S, with Gal(B_G/B) = G_B".
   - **:374 (t_1..t_4):** the "capped primes" are named in Definition tw:local-generators, not in Lemma tw:base. **Fix:** cite both.
   - **:361-364 vs κ:** see A.4.
9. **:192 and :357.** "The dependency index (Section B)". In the table of contents and in the heading it is "Appendix B" (line 355 says "Appendix A" for the shell weights).
   - **Fix:** write `Appendix~\ref{dep:section}`.

### B.3 Body sections, from the readers; minor unless marked

- **geometry.tex:37 and :130-131.** \mathcal O_K^1, "capitulation kernel", w_K, h_rel, h_cap and Reg^1 appear before Definition geo:relative-units and Proposition geo:mass.
  - **Fix:** add forward references.
- **geometry.tex:290-293 and :331-335.** J, and H and J in Lemma geo:selection, are used before or without Definition geo:exponents (:315).
  - **Fix:** add the reference.
- **geometry.tex:386 and :662.** "Ordered edges" and "real-place profile" are used before Definitions geo:counts and geo:profiles.
- **analytic.tex:78-79.** \mathcal L_F is used in the opener and defined at :110.
- **analytic.tex:453.** b_TV is used before Proposition an:signed introduces it.
- **analytic.tex:369-370.** Cites tw:base(d) for "the six primes of S lie above 2, 3, 5"; part (c) gives the primes.
  - **Fix:** cite "(c), (d)".
- **genus-field.tex:325.** "the remark following it" refers to an unnumbered paragraph, but reads like a numbered Remark.
- **certificate.tex:89-97, Lemma cert:places.** Uses (e_r, f_r) without citing Definition cert:effective-types. g_p, k_p and Q_p are never defined.
  - **Fix:** add "(e_r, f_r) of Definition cert:effective-types, and g_p = g_r, k_p = k_r, Q_p = Q_r for p above r".
- **certificate.tex:313-315.** "when θ is the value of θ for F" is circular.
  - **Fix:** "at θ = c/d for F".
- **limits.tex:184-195, lim:B.** f is used for f_r, for f_R and for f_j = f_{K_j}(p) in one statement and proof. S_p sits beside the global S, and g_r is redefined.
- **profiles.tex:514-551, pf:mass.** M_Q (a coefficient bound) and M_i(l,r) (a moment) appear in one statement. Pre-existing.
- **tower.tex:1416-1417 and lvalues.tex:201.** A summation index has the same letter as a degree or gamma index. Pre-existing.
- **dihedral.tex:357-358 vs :299-300.** β_i, F_{0,i} (census index i = 1..15) and β_o, F_{0,o} (form number o) are the same symbols under two index conventions, so β_7, F_{0,7} and β_17 are ambiguous. Both conventions meet in the proof of dh:pattern-lemma(e).
  - **Fix:** write β^c_i and F^c_{0,i}.
- **dihedral.tex: φ, φ_o and φ_M.** φ and φ_o (the associated linear map) and φ_M (the quotient homomorphism) appear together in the proofs of dh:detection(b) and dh:EW.
  - **Fix:** rename the homomorphism, for example π_M.
- **dihedral.tex:132-133.** σ is scoped "in this lemma", but dh:beta-exists (:243-256) uses σ(β)/β and t_σ.
- **dihedral.tex:115.** ψ_o is introduced only inside the computer-assisted proof of dh:27.
  - **Fix:** move it into the statement (see B.2 item 8).
- **Pre-existing in dihedral.tex:** a bare r in "4 = 2^{r/2}" (:604); Z(H) for a centre (:583) against Z(s) in the notation table; italic N_{B/Q} (:385).

---

## C. Statements

Each item gives the location, what is wrong, and a suggested fix.

1. **tower.tex:1132-1134 (introduced by the revision).**
   - The text reads: "Its kernel is $C_{\overline G}(\iota)\cap D_2\overline G$, where $C_{\overline G}(\iota)=\{\dots\}$ is the centralizer of $\iota$; it therefore has order $2^{33}$."
   - "It" now reads as the centralizer, which has order 2^34 (:1137). [verified]
   - **Fix:** end the sentence after "centralizer of ι." and continue "The kernel therefore has order 2^{15+26-8} = 2^{33}."
2. **tower.tex:1599-1601, opener of "The Fields".**
   - It says Theorem tw:field-family is used "in Section geo and Section cert".
   - The theorem is also used in genus-field (gf:in-tower), analytic (an:family, an:selected-def, an:selected-lemma) and dihedral (dh:floor-sum); see the "used by" row at dependency-index.tex:48. [verified]
   - **Fix:** "used in Sections 3-5, 8 and 11".
3. **tower.tex:639-640.** It says the capped primes' vectors come "from Lemma tw:base(e)", but (e) covers only t_3 and t_4.
   - **Fix:** "at t_3, t_4 also from Lemma tw:base(e)".
4. **analytic.tex:866-867, Lemma an:afe-range.** It claims "the hypotheses of Lemma an:tails hold", but the proof checks only the conditions on t(N+1).
   - **Fix:** "the conditions on t(N+1) in Lemma an:tails hold".
5. **analytic.tex:968-971, opener of the P_4 subsection.** It defines P_4 as the free primes "whose residue degree in every K is divisible by 4". Definition an:P4 actually uses Frobenius vectors outside Σ_2; divisibility by 4 is a consequence (Lemma an:census-degree).
   - **Fix:** reword.
6. **analytic.tex:735, opener.** It says both kernel-enclosure lemmas are used in Lemma an:row; an:row cites only an:binning.
7. **ceiling.tex:9-11.** "Lemma ce:values bounds the right-hand side of Proposition an:signed". It bounds the right-hand side minus Z_sel(1).
   - **Fix:** "bounds the terms other than Z_sel(1)".
8. **finite-windows.tex:743-747.** "The certificate does not use Corollary fw:uniform-types at 41". In fact it does not use it at all (certificate.tex:84-87). [verified]
   - **Fix:** "does not use Corollary fw:uniform-types, since the types at 41 are not uniform".
9. **introduction.tex:163.** "The proof has four parts, which meet only in the final inequality."
   - This is false as stated: Part (I) feeds (II) directly (dashed arrows tw:GB-presentation → dh:detection, tw:quadratic-layer → dh:census, dh:EW, lv:values), and (III) feeds (IV) (fw:transfer, fw:shell-lemma, pf:mass → cert:*).
   - **Fix:** "Parts (II)-(IV) apply to the fields of (I); (II) and (III) are independent and meet only in the final inequality (IV)".
10. **introduction.tex:179.** "the kernel (Lemma ce:values)". The kernel conditions are Lemma ce:kernel; ce:values bounds its values.
    - **Fix:** "the kernel (Lemmas ce:kernel and ce:values)".
11. **limits.tex:91-96.** "The sum of the credits is at least G_p" is a substantive inequality, stated in unnumbered prose and used without citation in the proof of lim:B (around :217).
    - **Fix:** make it lim:credits(b) and cite it.
12. **limits.tex:182-198.** Narrowed hypothesis (A.3).
13. **analytic.tex:332-335.** A new claim sits between the statement and the proof of an:prime-budget (A.2).
14. **introduction.tex:226-227.** Lemma dh:detection is cited for "each realized by an explicit field of degree 8", but the existence of the defining elements for all 27 forms is Lemma dh:beta-exists.
    - **Fix:** cite both.
15. **introduction.tex:237-240.** Lemma dh:EW is cited for "Hecke L-functions of quadratic characters of quartic/octic fields"; that identification is Lemma dh:Lfunctions.
    - **Fix:** cite both.
16. **dihedral.tex:242, 253.** "These 22 elements": forms 7, 17, 20 and 24 are both census forms and table forms, so there are 18 distinct elements checked 22 times. The old text also said 22.
    - **Fix:** "the 18 elements (22 checks)".
- All new dihedral lemmas have complete hypotheses and proofs that establish them.
- **Opening paragraphs (goal 3).** Every section and subsection now opens with such a paragraph, and the "used in" claims the readers checked are accurate apart from items 2, 6 and 8 above. Many subsections in profiles, certificate and geometry say what they prove but not where it is used; the section openers cover it.
- **Repetition.** limits.tex:265-267 repeats a sentence ("This subsection lists how the intermediate exponents … The intermediate exponents of Table … use …"). At limits.tex:26, "This gave the exponent 1.042925" has an unclear subject. The "effective type at 41 is a counting device" explanation now appears four times (certificate.tex:76-81, 84-87 and 110-118; finite-windows.tex:745-747).

---

## D. Figure 1 and the dependency index

### D.1 How they are made

tools/depgraph.py takes as the dependencies of a labelled statement the `\ref/\eqref` inside the statement and its first unheaded proof, plus any proof headed "Proof of … \ref{X}". It treats two kinds of citation as non-dependencies:
- `\fref`;
- a citation of a later statement inside a definition or remark.

The figure draws the reduction of that graph to 26 shown statements: B uses A directly or through unshown statements. It then removes every edge implied by a path through other shown statements (reduced_edges, lines 141-153). Arrows from Theorem tw:field-family are omitted.

### D.2 Fifteen arrows checked against the proofs

| Arrow | Basis in the text | Verdict |
|---|---|---|
| an:ceiling → thm:main | certificate.tex:343-345 "By Theorem an:ceiling" | correct |
| cert:lower-margin → thm:main | certificate.tex:363-364 | correct |
| cert:enclosures → cert:lower-margin | proof cites cert:enclosures(a), (h) | correct |
| cert:exact → cert:lower-margin | proof cites cert:exact(c), (d) | correct |
| cert:places → cert:enclosures | (f) bounds "the numbers H of Lemma cert:places" | correct |
| **fw:transfer → cert:places** | proof of cert:places (certificate.tex:115-118): "Corollary fw:uniform-types … is not used at 41; Proposition fw:transfer is applied directly". A pointer, not a use | **spurious** |
| **fw:shell-lemma → cert:exact** | certificate.tex:185-187, parenthetical "(Lemma fw:shell-lemma needs only …)". The finite checks do not use the lemma | **spurious** (pointer) |
| **pf:mass → cert:exact** | only through Definition cert:data(d), "In Proposition pf:mass we partition …", a parameter choice. Logically cert:exact(c) verifies a hypothesis of pf:mass, the reverse direction | **spurious** |
| pf:mass → cert:enclosures | (a) "by Proposition pf:mass" | correct |
| ce:kernel → an:ceiling; ce:values → an:ceiling; dh:floors-valid → an:ceiling | ceiling.tex:147-161 | correct |
| dh:census → ce:values; lv:values → ce:values | ceiling.tex:122-128 | correct |
| dh:EW → ce:values | through Lemma dh:delta-sel, whose proof uses dh:EW(e) | correct |
| an:signed → ce:values | only through Definition ce:kernel-def, "the kernel of Proposition an:signed with n = 21" (naming) | weak; notational |
| dh:census → dh:floors-valid; dh:EW → dh:floors-valid | dihedral.tex:824-838 | correct |
| tw:retained-quotient → tw:infinite; tw:quadratic-layer → tw:retained-quotient; tw:GB-presentation → dh:detection; an:limit → an:signed; an:signed → ce:kernel; geo:mass, geo:selection → geo:transfer; tw:infinite → tw:field-family | the citations are genuine uses (tower.tex:1550-1556, 1085-1120; dihedral.tex:197; analytic.tex:478, 510, 518; ceiling.tex:52-53; geometry.tex:824, 861; tower.tex:1672) | correct |

### D.3 Caption and figure accuracy

1. **The caption omits the transitive reduction.**
   - The caption says: "An arrow goes from a statement to each statement whose proof uses it, directly or through statements not shown".
   - The figure drops every such edge that is implied by a path of shown arrows: 27 pairs. Ten of them are direct citations: an:signed → an:ceiling, cert:exact → thm:main, cert:places → cert:lower-margin, cert:places → thm:main, fw:transfer → thm:main, pf:mass → cert:lower-margin, tw:GB-presentation → tw:infinite, tw:GB-presentation → tw:retained-quotient, tw:retained-quotient → tw:field-family, tw:field-family → thm:main.
   - The tool's docstring (depgraph.py lines 17-19) has the same gap.
   - **Fix:** add "Arrows implied by a chain of drawn arrows are left out."
2. **The pointer citations change the picture.**
   - Because of the spurious fw:transfer → cert:places, the reduction hides fw:transfer → thm:main. The figure suggests that Part (III) enters the proof through the place-count lemma, whereas the proof of Theorem 1.1 applies Proposition fw:transfer directly (certificate.tex:347-352).
   - **Fix:** use `\fref` at certificate.tex:116-118 (both refs) and at :185-186, then regenerate.
   - According to the geometry reader's simulation, this removes fw:transfer → cert:places and adds fw:transfer → thm:main and fw:shell-lemma → cert:enclosures.
   - pf:mass → cert:exact goes away if Definition cert:data(d) uses `\fref`.
3. **Three arrows are drawn through other boxes.** The router (depgraph.py `_route`) falls back to a straight line when it finds no free path. Checked against the true box sizes:
   - Lemma 5.5 → Prop 6.5 crosses Prop 3.8 and Lemma 5.13;
   - Lemma 2.29 → Prop 5.12 crosses Lemma 5.5 and Prop 3.8;
   - Prop 10.21 → Prop 11.6 crosses Prop 9.26 and Lemma 11.3.
   - In the rendering at 220 dpi the line from 5.5 runs through the lower part of the "factorization of ζ_E" box. The S-shaped dashed curve Lemma 2.29 → Lemma 5.13 ends beside the top-left corner of Prop 6.5, so its target is ambiguous.
   - **Fix:** move dh:detection or gf:factorization one column, or route through explicit waypoints.
4. **Readability otherwise.**
   - Good: legible at print size; the colour legend is clear; dashed versus solid is visible; the figure fits the text width (no overfull box).
   - Prop 10.21 (green, Part III) sits in the orange Part II area under Lemma 4.13.
   - "Dependency Index" in the caption has no reference.
5. **"lists the complete graph" is an overstatement** (introduction.tex:192; caption). See D.4.

### D.4 Dependency index: 17 rows spot-checked

Rows verified correct against the text:
- thm:main "uses";
- tw:infinite;
- tw:field-family "uses" (it includes Definition geo:uniform-types, a precise forward reference from Section 2 to Section 8);
- an:ceiling;
- dh:detection;
- dh:floors-valid;
- ce:values;
- ce:kernel;
- dh:census.

Rows with defects:

| Row (dependency-index.tex line) | Defect |
|---|---|
| Thm thm:main (:11) "used by" | Rem an:base-ceiling and Rem an:lean-hypothesis are listed. Both say thm:main is *not* used or proved (analytic.tex:1078, 1108); remarks citing an earlier statement count as uses. **Fix:** `\fref` |
| Lem cert:places (:182) | "uses" Prop fw:transfer and Cor fw:uniform-types (pointers, see D.2). It misses Def cert:data and Def cert:effective-types, which it uses without `\ref` |
| Prop fw:transfer (:161) "used by" | lists Lem cert:places (false). Misses Lem cert:lower-margin, which cites `\eqref{fw:margin}` inside fw:transfer |
| Prop cert:exact (:184) | "uses" Lem fw:shell-lemma (pointer). Misses pf:overlap (`\eqref{pf:cross-threshold}`) and pf:tube-constant (q_0) |
| Prop cert:enclosures (:185) | misses pf:overlap, pf:functional and pf:gaussian (only their equations are cited), and fw:shell-lemma through the prose equation (cert:finite-factor) |
| Lem cert:lower-margin (:187) | misses fw:transfer (`\eqref{fw:margin}`) |
| Prop lv:values (:117) | misses Lem dh:EW: it cites only `\eqref{dh:YW}`, which lies inside dh:EW. So the index and the figure have no dh:EW → lv:values |
| Lem dh:EW (:103) "used by" | misses lv:values (same cause) and lv:coefficients (uses E_{W''} ⊆ K without `\ref`) |
| Prop an:signed (:73) | misses Def an:floor-def and Def an:selected-def ("Let (f^0_p) be a system of floors", Z_sel, T_sel, q_min, all without `\ref`) |
| Def an:floor-def (:72) "used by" | only dh:floors-valid; an:signed, ce:values and others use the notion |
| Def ce:kernel-def (:118) | "uses" Prop an:signed (naming only) |

**Systematic causes, with counts from a scan of the sources:**
- **About 31 uses are cited only by `\eqref` of an equation inside another statement.** Examples:
  - geo:mass → geo:norm-one, which then shows as used by nothing;
  - fw:shell-lemma → fw:gram-lemma, which shows as used by nothing;
  - geo:transfer and fw:uniform-types → geo:exponents, which shows as used by nothing;
  - an:genus-value → an:row;
  - dh:floor-sum and dh:delta-sel → an:local-contribution;
  - lv:values → dh:EW;
  - cert:* → pf:overlap and pf:functional;
  - pf:admissible → pf:hyperbola.
- **Bare item labels.** Lemma tw:row-properties shows "used by --" because its items are cited as bare "(F1)"–"(F4)" (tower.tex:1262, 1278, 1353, 1382, 1402, 1407). tw:hilbert-properties is cited as bare "(h1)–(h3)".
- **Uses without any `\ref`:**
  - geo:admissible ("admissible with Fourier constants");
  - an:floor-def;
  - lim:credits (R, I, S, G in lim:A, lim:B and lim:D);
  - fw:local-functional and fw:shell-profile in the statement of fw:transfer;
  - cert:effective-types.
- **Ranges.** "Lemmas an:balanced-afe--an:binning" (analytic.tex:953) records only the two endpoints.
- **Prose outside a proof environment.** an:afe-range is cited only before an:row (:902), so it shows "used by --".
- **Other pointer `\ref`s that become "uses":**
  - geo:phi-omega(a) → geo:unfold-lemma ("by the remark before");
  - Rem ce:comparison → ce:kernel ("checked by");
  - Cor gf:conductors → Rem gf:checks ("also prints");
  - fw:local-functional, fw:endpoint-law → geo:profiles ("as for");
  - fw:transfer → geo:window, geo:counts ("plays the role of", "the analogue of").
- **The dihedral section** (dihedral reader, with the index rows checked):
  - dh:quadratic, dh:dihedral-type, dh:census-basis and dh:vector-zero show "used by --", although dh:27, dh:detection, dh:pattern-lemma, dh:census, dh:floors and dh:EW use them.
  - The use of dh:vector-zero and dh:beta-exists in the census sits in prose at dihedral.tex:442-451, outside the proof of dh:census.
  - dh:residue and dh:Lfunctions use dh:EW objects (G_{W''}, ρ_o) without `\ref`.
  - Pointer "uses": dh:floors → dh:census (:811, "counted in the last column of …") and dh:EW → an:genus-value (:561, cited only for the definition of Y_E). The real use, ∏_w L(s, χ_w) = ζ_E, is gf:factorization, which is uncited there; the figure arrow gf:factorization → dh:EW is right only by way of this pointer.
- **Overall effect.** 53 of the 187 rows have an empty "used by" column. 33 of these are not remarks, including widely used statements such as Def tw:rd, Def an:family (the family \mathcal K), Def dh:dihedral-type, Def geo:admissible, Def fw:local-functional, Lem geo:norm-one, Lem fw:gram-lemma and Lem an:row.
- **Suggested fixes:**
  - (a) Make depgraph.py map equation labels to the statement that contains them, and expand ranges.
  - (b) Use `\fref` for the pointers listed.
  - (c) Add `\ref` at first use for the uncited definitions.
  - (d) Or soften "complete graph" to "the graph of explicit citations".

---

## E. Build

- `nice -n 10 make` ran in the paper directory: pdflatex, bibtex and three more pdflatex passes. Exit 0.
- **main.log:**
  - 0 errors;
  - no "LaTeX Warning" of any kind, so no undefined or multiply-defined references or citations;
  - **0 overfull boxes**;
  - 47 underfull hbox warnings:
    - 45 come from the ragged p-columns of the generated dependency index (sections/dependency-index.tex);
    - 2 (badness 10000) come from the "defined in" column of the notation table, at introduction.tex:381 and :392 ("Definition 2.44," and "Proposition 4.19," alone on a line).
  - The underfull boxes are cosmetic. The notation-table ones go away with a wider third column or `\raggedright`.
- **PDF.** "Output written on main.pdf (99 pages)"; master's PDF has 83. The rebuilt PDF's pdftotext output is identical to that of the committed PDF; only the creation date differed.
- **Generated files.** `python3 tools/depgraph.py --check` reports "187 statements, 321 citations" and exit 0, so proof-structure.tex and dependency-index.tex are current.
- **Restoring the tree.** make rewrote the tracked main.pdf; it was restored with `git checkout -- main.pdf`. The ignored intermediates (aux, bbl, blg, log, out, toc) were restored from a backup taken before the build. `git status` is clean, and main.pdf has its committed md5 (bc62568e…).

---

## Pre-existing issues noticed (not introduced by the revision)

- **ceiling.tex:127-144, Lemma ce:values.** The printed rounded numbers do not add up to the stated bound:
  - 0.00056180334 - 0.0000757399 + b_TV·1.0734268715 = 0.000607836111, which exceeds 0.00060783605369 by 5.8e-11. [verified, exact rational arithmetic]
  - The cause is the outward rounding of 0.0000757399 to 1e-10. The proof says the unrounded total is below the bound, but a reader cannot check that from the digits shown. The text is unchanged from master.
  - **Fix:** print the two partial sums to about 12 significant digits, or print the unrounded total.
- **certificate.tex:123-132.** The formula (cert:finite-factor), on which cert:enclosures(e) depends, is derived in prose rather than in a numbered statement.

---

## What was not checked

- **Supplementary programs:** I ran none of them. Readers only read the docstrings or lines of a few: dcoef4.c, dafe.py, ceiling41.py, check255.gp, dihedral_ceiling3.py and the witness JSONs.
- **Certified values:** no certified enclosure, L-value, census count or margin was recomputed. The exceptions are the arithmetic noted above: an:afe-range, Z_sel(1), the ce:values sum and the place counts.
- **Unchanged mathematics:** passages the diff left unchanged were not re-verified beyond spot checks.
- **Rendering:** the PDF was not inspected page by page; only page 4 (Figure 1) was rendered.
- **Index coverage:** only 17 of 187 index rows were checked by hand. The eqref scan covers all rows for that one failure mode.
- **Other bibliographic citations:** apart from TV Prop. 3.1 and the 0418235 sections, I did not check them against their sources.
