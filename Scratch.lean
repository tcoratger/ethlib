import EthLib.Cryptography.Proofs.Kzg.CellVerifier
import EthLib.Base.Proofs.MapM

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

attribute [-instance] Fin.instNatPow

/-- A map over an array succeeds when the function succeeds on every entry. -/
theorem array_mapM_exists_ok {ε α β : Type} {f : α → Except ε β} {xs : Array α}
    (h : ∀ x ∈ xs, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys := by
  obtain ⟨ys, hys⟩ := Base.mapM_exists_ok (f := f) (xs := xs.toList)
    fun x hx => h x (Array.mem_toList_iff.mp hx)
  refine ⟨ys.toArray, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hys]
  rfl

/-- A map over an array that succeeds on every entry returns no error. -/
theorem array_mapM_ne_error {ε α β : Type} {f : α → Except ε β} {xs : Array α} {e : ε}
    (h : ∀ x ∈ xs, ∃ y, f x = .ok y) : xs.mapM f ≠ .error e := by
  obtain ⟨ys, hys⟩ := array_mapM_exists_ok h
  rw [hys]
  exact fun h => nomatch h

/-- The interpolation of 64 values on a coset succeeds. -/
theorem interpolateCosetEvals_ok {h : Fr} {evals : CosetEvals}
    (hsz : evals.size = FIELD_ELEMENTS_PER_CELL) :
    ∃ p, interpolateCosetEvals h evals = .ok p := by
  unfold interpolateCosetEvals
  rw [ite_eq_right (not_not.mpr hsz)]
  exact ⟨_, rfl⟩

/-- The sum of the interpolations succeeds when every cell has 64 values. -/
theorem sumInterp_ok :
    ∀ (L : List (Fr × CosetEvals × Fr)) (init : PolynomialCoeff),
      init.size = FIELD_ELEMENTS_PER_CELL → (∀ e ∈ L, e.2.1.size = FIELD_ELEMENTS_PER_CELL) →
      ∃ acc, L.foldlM (fun sumInterp (e : Fr × CosetEvals × Fr) => do
          let interp ← interpolateCosetEvals e.1 e.2.1
          let scaled ← multiplyPolynomialcoeff #[e.2.2] interp
          pure (addPolynomialcoeff sumInterp scaled)) init = .ok acc
  | [], init, _, _ => ⟨init, rfl⟩
  | e :: L, init, hinit, hL => by
    obtain ⟨interp, hi⟩ := interpolateCosetEvals_ok (h := e.1) (hL e List.mem_cons_self)
    obtain ⟨hisz, -⟩ := size_of_interpolateCosetEvals hi
    obtain ⟨scaled, hs, hssz⟩ := multiplyPolynomialcoeff_ok_of_le (a := #[e.2.2]) (b := interp)
      (by simp [hisz]; decide)
    have hnext : (addPolynomialcoeff init scaled).size = FIELD_ELEMENTS_PER_CELL := by
      rw [size_addPolynomialcoeff, hinit, hssz, hisz]
      simp; decide
    obtain ⟨acc, hacc⟩ := sumInterp_ok L _ hnext fun e' he' => hL e' (List.mem_cons_of_mem e he')
    refine ⟨acc, ?_⟩
    simp only [List.foldlM_cons, bind, Except.bind, hi, hs, pure, Except.pure]
    exact hacc

/-- **The core check of cells returns.**

The cells, their values and the proofs are as many as the commitment indices.

Each commitment index names a commitment, and no commitment repeats.

The commitments and the proofs decode, each cell index is below 128, and each cell has 64 values.

Then the core check returns a verdict, with no error. -/
theorem verifyCellKzgProofBatchImpl_ok {s : TrustedSetup} {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof} {G Q : Array G1}
    (h₁ : cellIndices.size = commitmentIndices.size)
    (h₂ : cosetsEvals.size = commitmentIndices.size) (h₃ : proofs.size = commitmentIndices.size)
    (h₄ : ∀ i ∈ commitmentIndices, i < commitments.size)
    (h₅ : (commitments.zipIdx.any fun (c, i) => commitments.idxOf? c ≠ some i) = false)
    (hG : commitments.mapM uncompressG1 = .ok G) (hQ : proofs.mapM uncompressG1 = .ok Q)
    (hci : ∀ i ∈ cellIndices, i < CELLS_PER_EXT_BLOB)
    (hev : ∀ e ∈ cosetsEvals, e.size = FIELD_ELEMENTS_PER_CELL) :
    ∃ b, verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices cosetsEvals
      proofs = .ok b := by
  have h₄' : commitmentIndices.any (· ≥ commitments.size) = false :=
    Array.any_eq_false'.mpr fun i hi => by simpa using h₄ i hi
  cases hI : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices cosetsEvals
    proofs with
  | ok b => exact ⟨b, rfl⟩
  | error e =>
  exfalso
  unfold verifyCellKzgProofBatchImpl at hI
  simp only [h₁, h₂, h₃, h₄', h₅, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    bind, Except.bind, hG, hQ] at hI
  set n := commitmentIndices.size
  set r := computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices cellIndices
    cosetsEvals proofs
  have hrp : (computePowers r n).size = n := size_computePowers r n
  obtain ⟨hQsz, -⟩ := array_mapM_ok hQ
  obtain ⟨hGsz, -⟩ := array_mapM_ok hG
  have hWsz : (Array.foldl (fun weights (e : Nat × Fr) => weights.modify e.1 (· + e.2))
      (Array.replicate commitments.size Fr.zero) (commitmentIndices.zip (computePowers r n))).size =
      commitments.size := by
    rw [← Array.foldl_toList]
    generalize (commitmentIndices.zip (computePowers r n)).toList = L
    suffices ∀ (L : List (Nat × Fr)) (W : Array Fr),
        (L.foldl (fun weights (e : Nat × Fr) => weights.modify e.1 (· + e.2)) W).size = W.size by
      rw [this, Array.size_replicate]
    intro L
    induction L with
    | nil => intro W; rfl
    | cons e L ih => intro W; rw [List.foldl_cons, ih, Array.size_modify]
  have lincomb : ∀ {P : Array G1} {a : Array Fr}, P.size = a.size →
      g1LincombPoints P a = .ok (G1.msm P a) := fun h => g1LincombPoints_eq_msm h
  rw [lincomb (hQsz.trans (h₃.trans hrp.symm)), lincomb (hGsz.trans hWsz.symm)] at hI
  dsimp only at hI
  -- The shifts exist, since every cell index is below 128.
  split at hI
  · rename_i err hsh
    refine array_mapM_ne_error (fun i hi => ?_) hsh
    have hlt : FIELD_ELEMENTS_PER_CELL * i < (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB).size := by
      have := hci i hi
      rw [size_rootsOfUnityBrp]
      change 64 * i < 8192
      change i < 128 at this
      omega
    exact ⟨_, by simp only [hlt, ↓reduceDIte]; rfl⟩
  rename_i shifts hsh
  have hshsz : shifts.size = n := (array_mapM_ok hsh).1.trans h₁
  -- The sum of the interpolations exists, since every cell has 64 values.
  have hall : ∀ e ∈ (shifts.zip (cosetsEvals.zip (computePowers r n))).toList,
      e.2.1.size = FIELD_ELEMENTS_PER_CELL := fun e he =>
    hev _ (Array.of_mem_zip (Array.of_mem_zip (Array.mem_toList_iff.mp he)).2).1
  split at hI
  · rename_i err hsum
    obtain ⟨acc, hacc⟩ := sumInterp_ok _ (Array.replicate FIELD_ELEMENTS_PER_CELL Fr.zero)
      Array.size_replicate hall
    rw [Array.foldlM_toList] at hacc
    exact absurd (hsum.symm.trans hacc) fun h => nomatch h
  rename_i sumInterp hsum
  obtain ⟨hsisz, -, -⟩ := sumInterp_spec 0 (shifts.zip (cosetsEvals.zip (computePowers r n))).toList
    (Array.replicate FIELD_ELEMENTS_PER_CELL Fr.zero) sumInterp Array.size_replicate
    (by rw [Array.foldlM_toList]; exact hsum)
  have hmono : (s.g1Monomial.toArray.extract 0 FIELD_ELEMENTS_PER_CELL).size = sumInterp.size := by
    rw [hsisz, Array.size_extract, Vector.size_toArray]
    rfl
  have hwrp : Q.size =
      (Array.zipWith (fun rPower shift => rPower * shift ^ Fr.ofNat FIELD_ELEMENTS_PER_CELL)
        (computePowers r n) shifts).size := by
    rw [Array.size_zipWith, hrp, hshsz, hQsz, h₃, Nat.min_self]
  rw [lincomb hmono, lincomb hwrp] at hI
  cases hI

end EthLib.Cryptography.Kzg
