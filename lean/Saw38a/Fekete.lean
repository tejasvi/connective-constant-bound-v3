import Saw38a.Spec

/-!
# The connective constant exists (Fekete)

* Basic facts about `walk`: `walk_zero`, `walk_succ`, and the walks of the two halves of a step sequence of length
  `m + n` (`walk_pre`, `walk_suf`).
* Submultiplicativity `c_{m+n} ≤ c_m c_n` (`sawCount_add_le`): the two halves of a self-avoiding walk are
  self-avoiding, and a step sequence is determined by its halves.
* `c_n ≥ 1` (`sawCount_pos`): the straight walk.
* Fekete's lemma (`Subadditive.tendsto_lim` of Mathlib) for `n ↦ log c_n` gives `log c_n / n → L`, hence
  `c_n ^ (1/n) = exp (log c_n / n) → exp L` (`connective_constant_exists'`, the statement of
  `connective_constant_exists`).
-/

namespace Saw38a

open Filter Topology

section WalkAPI

variable {m n : ℕ}

theorem walk_zero (s : Fin n → Fin 4) : walk s 0 = 0 := by
  simp [walk]

theorem walk_succ (s : Fin n → Fin 4) (i : Fin n) :
    walk s i.succ = walk s i.castSucc + dir (s i) := by
  simp only [walk, Fin.val_succ, Fin.val_castSucc]
  have key : ∀ j : Fin n, (if (j : ℕ) < (i : ℕ) + 1 then dir (s j) else 0) =
      (if (j : ℕ) < (i : ℕ) then dir (s j) else 0) + (if j = i then dir (s j) else 0) := by
    intro j
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · have hne : j ≠ i := fun e => by subst e; omega
      have h1 : (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, hne, h1]
    · have he : j = i := Fin.ext h
      subst he
      simp
    · have h1 : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
      have h2 : ¬ (j : ℕ) < (i : ℕ) := by omega
      have h3 : j ≠ i := fun e => by subst e; omega
      simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The first `m` steps of a step sequence of length `m + n`. -/
def pre (m : ℕ) {n : ℕ} (s : Fin (m + n) → Fin 4) : Fin m → Fin 4 := fun i => s (Fin.castAdd n i)

/-- The last `n` steps of a step sequence of length `m + n`. -/
def suf (m : ℕ) {n : ℕ} (s : Fin (m + n) → Fin 4) : Fin n → Fin 4 := fun i => s (Fin.natAdd m i)

theorem walk_pre (s : Fin (m + n) → Fin 4) (i : Fin (m + 1)) :
    walk (pre m s) i = walk s ⟨i, by have := i.isLt; omega⟩ := by
  simp only [walk, pre]
  rw [Fin.sum_univ_add]
  have h : ∀ k : Fin n, ¬ (m + (k : ℕ) < (i : ℕ)) := fun k => by have := i.isLt; omega
  simp [h]

theorem walk_suf (s : Fin (m + n) → Fin 4) (j : Fin (n + 1)) :
    walk s ⟨m + j, by have := j.isLt; omega⟩ = walk s ⟨m, by omega⟩ + walk (suf m s) j := by
  simp only [walk, suf]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have h1 : ∀ k : Fin m, (k : ℕ) < m + j := fun k => by have := k.isLt; omega
  have h3 : ∀ k : Fin n, (m + (k : ℕ) < m + j) ↔ (k : ℕ) < j := fun k => by omega
  have h4 : ∀ k : Fin n, ¬ (m + (k : ℕ) < m) := fun k => by omega
  simp [h1, h3, h4]

theorem injective_pre {s : Fin (m + n) → Fin 4} (hs : Function.Injective (walk s)) :
    Function.Injective (walk (pre m s)) := by
  intro a b hab
  rw [walk_pre, walk_pre] at hab
  have h := congrArg Fin.val (hs hab)
  exact Fin.ext h

theorem injective_suf {s : Fin (m + n) → Fin 4} (hs : Function.Injective (walk s)) :
    Function.Injective (walk (suf m s)) := by
  intro a b hab
  have h : walk s ⟨m + a, by have := a.isLt; omega⟩ = walk s ⟨m + b, by have := b.isLt; omega⟩ := by
    rw [walk_suf, walk_suf, hab]
  have h' := congrArg Fin.val (hs h)
  simp only at h'
  exact Fin.ext (by omega)

/-- The straight walk `0, e₁, 2e₁, …`. -/
theorem walk_straight_fst (i : Fin (n + 1)) :
    (walk (fun _ : Fin n => (0 : Fin 4)) i).1 = (i : ℕ) := by
  induction i using Fin.induction with
  | zero => simp [walk_zero]
  | succ i ih => rw [walk_succ, Prod.fst_add, ih]; simp [dir]

theorem injective_walk_straight : Function.Injective (walk (fun _ : Fin n => (0 : Fin 4))) := by
  intro a b hab
  have h := congrArg Prod.fst hab
  rw [walk_straight_fst, walk_straight_fst] at h
  exact Fin.ext (by exact_mod_cast h)

end WalkAPI

/-- `c_{m+n} ≤ c_m c_n`. -/
theorem sawCount_add_le (m n : ℕ) : sawCount (m + n) ≤ sawCount m * sawCount n := by
  unfold sawCount
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun s => (pre m s, suf m s)) ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq]
    exact ⟨injective_pre hs, injective_suf hs⟩
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · exact congrFun h.1 k
    · exact congrFun h.2 k

/-- `c_n ≥ 1`. -/
theorem sawCount_pos (n : ℕ) : 0 < sawCount n := by
  unfold sawCount
  exact Finset.card_pos.2 ⟨fun _ => 0, by simp [injective_walk_straight]⟩

/-- `log c_n`. -/
noncomputable def logSaw (n : ℕ) : ℝ := Real.log (sawCount n)

theorem one_le_sawCount_real (n : ℕ) : (1 : ℝ) ≤ sawCount n := by
  exact_mod_cast sawCount_pos n

theorem logSaw_nonneg (n : ℕ) : 0 ≤ logSaw n := Real.log_nonneg (one_le_sawCount_real n)

theorem logSaw_subadditive : Subadditive logSaw := by
  intro m n
  unfold logSaw
  have hm : (0 : ℝ) < sawCount m := by exact_mod_cast sawCount_pos m
  have hn : (0 : ℝ) < sawCount n := by exact_mod_cast sawCount_pos n
  rw [← Real.log_mul hm.ne' hn.ne']
  apply Real.log_le_log (by exact_mod_cast sawCount_pos (m + n))
  exact_mod_cast sawCount_add_le m n

/-- Fekete: `log c_n / n` converges. -/
theorem tendsto_logSaw_div :
    Tendsto (fun n : ℕ => logSaw n / n) atTop (𝓝 logSaw_subadditive.lim) :=
  logSaw_subadditive.tendsto_lim
    ⟨0, fun _ ⟨n, hn⟩ => hn ▸ div_nonneg (logSaw_nonneg n) (Nat.cast_nonneg n)⟩

/-- The connective constant `μ = exp (lim log c_n / n)`. -/
noncomputable def connMu : ℝ := Real.exp logSaw_subadditive.lim

theorem connMu_pos : 0 < connMu := Real.exp_pos _

theorem log_connMu : Real.log connMu = logSaw_subadditive.lim := Real.log_exp _

theorem sawCount_rpow (n : ℕ) : (sawCount n : ℝ) ^ ((1 : ℝ) / n) = Real.exp (logSaw n / n) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast sawCount_pos n)]
  unfold logSaw
  ring_nf

/-- `log c_n / n → log μ`. -/
theorem tendsto_log_sawCount_div :
    Tendsto (fun n : ℕ => Real.log (sawCount n) / n) atTop (𝓝 (Real.log connMu)) := by
  rw [log_connMu]
  exact tendsto_logSaw_div

/-- `c_n ^ (1/n) → μ`. -/
theorem tendsto_connMu :
    Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 connMu) := by
  simp_rw [sawCount_rpow]
  exact (Real.continuous_exp.tendsto _).comp tendsto_logSaw_div

/-- The statement of `connective_constant_exists`. -/
theorem connective_constant_exists' :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) :=
  ⟨connMu, tendsto_connMu⟩

end Saw38a
