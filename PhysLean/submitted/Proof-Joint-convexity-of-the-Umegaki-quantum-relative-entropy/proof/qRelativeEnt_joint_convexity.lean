-- EXCERPT of the added code (PhysLean branch feat/qrelent-joint-convexity, commit 720c9fff).
-- The contribution spans three files; this excerpt collects the added declarations for reading.
-- The exact change set is in qrelent-joint-convexity.patch (git show of the commit).
-- Reproduce all checks with ../verify.sh <your-physlib-checkout>.
--
-- Added declarations:
--   QuantumInfo/ClassicalInfo/Prob.lean : Mixable.mix_one           (@[simp]; partner of mix_zero)
--   QuantumInfo/Entropy/Relative.lean   : qRelativeEnt_ne_top_iff, qRelativeEnt_eq_top_iff
--   QuantumInfo/Entropy/DPI.lean        : the theorem + its supporting lemmas (below)

-- ── QuantumInfo/ClassicalInfo/Prob.lean (added next to `mix_zero`) ──────────────

/-- `(1 : Prob) [ x₁ ↔ x₂ ] = x₁` — the `p = 1` companion of `mix_zero`. -/
@[simp]
theorem mix_one [inst : Mixable U T] (x₁ x₂ : T) : (1 : Prob) [ x₁ ↔ x₂ : inst] = x₁ := by
  apply inst.to_U_inj
  simp [mix, mix_ab]

-- ── QuantumInfo/Entropy/Relative.lean (added next to `qRelativeEnt_ker`) ────────

/-- The quantum relative entropy is finite exactly when the support condition
`σ.M.ker ≤ ρ.M.ker` holds. -/
theorem qRelativeEnt_ne_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) ≠ ⊤ ↔ σ.M.ker ≤ ρ.M.ker := by
  rw [qRelativeEnt, SandwichedRelRentropy]
  simp only [zero_lt_one, ↓reduceDIte]
  split_ifs with h <;> simp [h]

/-- The quantum relative entropy is `⊤` exactly when the support condition fails. -/
theorem qRelativeEnt_eq_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) = ⊤ ↔ ¬ σ.M.ker ≤ ρ.M.ker := by
  simpa using (not_congr (qRelativeEnt_ne_top_iff (ρ := ρ) (σ := σ)))

-- ── QuantumInfo/Entropy/DPI.lean (the theorem and its supporting lemmas) ────────

/-! ## Joint Convexity of the Relative Entropy

Joint convexity of the (Umegaki) quantum relative entropy is derived from joint convexity
of the trace functional `Q̃_α` (`sandwichedTraceFunctional_jointly_convex`) by letting
`α → 1⁺`, in the same way that `sandwichedRenyiEntropy_DPI_eq_one` follows from the
`α > 1` case.

For `α > 1` and states with compatible kernels, `log x ≤ x - 1` gives
`D̃_α(ρ‖σ) = log (Q̃_α(ρ‖σ)) / (α - 1) ≤ (Q̃_α(ρ‖σ) - 1) / (α - 1)`, and the difference
quotient on the right is jointly convex in `(ρ, σ)` because `Q̃_α` is. As `α → 1⁺`, the
left-hand side tends to `𝐃(ρ‖σ)` (by `sandwichedRelRentropy.continuousOn`), and the
difference quotient tends to `𝐃(ρ‖σ)` as well (since `Q̃_α = exp ((α - 1) D̃_α)` and
`exp x ≤ 1 + x + x²` for `|x| ≤ 1`), so the convex combination passes to the limit.
-/

/-- As `α → 1⁺`, the sandwiched Rényi relative entropy `D̃_α(ρ‖σ)` tends to the relative
entropy `𝐃(ρ‖σ) = D̃_1(ρ‖σ)`, by continuity of `α ↦ D̃_α` on `(0, ∞)`. -/
theorem sandwichedRelRentropy_tendsto_qRelativeEnt (ρ σ : MState d) :
    Filter.Tendsto (fun α : ℝ => D̃_ α(ρ‖σ)) (𝓝[>] 1) (𝓝 𝐃(ρ‖σ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds
    ((sandwichedRelRentropy.continuousOn ρ σ).continuousAt (Ioi_mem_nhds zero_lt_one))

/-- As `α → 1⁺`, the difference quotient `(Q̃_α(ρ‖σ) - 1) / (α - 1)` is eventually bounded
above by a function tending to `𝐃(ρ‖σ).toReal`. This is the key estimate for transferring
joint convexity of the trace functional `Q̃_α` to the relative entropy `𝐃` in
`qRelativeEnt_joint_convexity`. -/
private lemma sandwichedTraceFunctional_sub_one_div_eventually_le
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    ∃ u : ℝ → ℝ, Filter.Tendsto u (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) ∧
      ∀ᶠ α in 𝓝[>] 1, (Q̃_ α(ρ‖σ) - 1) / (α - 1) ≤ u α := by
  set r : ℝ → ℝ := fun α => Real.log (Q̃_ α(ρ‖σ)) / (α - 1) with hr_def
  have h_ne : 𝐃(ρ‖σ) ≠ ⊤ := qRelativeEnt_ne_top_iff.mpr hker
  have h_r_nonneg : ∀ α : ℝ, 1 < α → 0 ≤ r α := by
    intro α hα
    have h := sandwichedRelRentropy_nonneg (ρ := ρ) (σ := σ) (α := α) (by linarith) hker
    rw [if_neg hα.ne'] at h
    simpa [hr_def, sandwichedTraceFunctional] using h
  have h_eq : ∀ α : ℝ, 1 < α → D̃_ α(ρ‖σ) = ENNReal.ofReal (r α) := fun α hα =>
    sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker
  -- `r` tends to `𝐃(ρ‖σ).toReal`, by continuity of `α ↦ D̃_α(ρ‖σ)` at `α = 1`.
  have h_r_tendsto : Filter.Tendsto r (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) := by
    refine Filter.Tendsto.congr' ?_ ((ENNReal.tendsto_toReal h_ne).comp
      (sandwichedRelRentropy_tendsto_qRelativeEnt ρ σ))
    filter_upwards [self_mem_nhdsWithin] with α (hα : 1 < α)
    simp only [Function.comp_apply, h_eq α hα, ENNReal.toReal_ofReal (h_r_nonneg α hα)]
  have h_eps : Filter.Tendsto (fun α : ℝ => (α - 1) * r α) (𝓝[>] 1) (𝓝 0) := by
    have h₁ : Filter.Tendsto (fun α : ℝ => α - 1) (𝓝[>] 1) (𝓝 0) := by
      simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using h₁.mul h_r_tendsto
  refine ⟨fun α => r α + ((α - 1) * r α) * r α, ?_, ?_⟩
  · simpa using h_r_tendsto.add (h_eps.mul h_r_tendsto)
  · -- Eventually `|(α - 1) * r α| ≤ 1`, so `exp x - 1 ≤ x + x²` applies with
    -- `x = (α - 1) * r α = log (Q̃_α)`.
    have h_small : ∀ᶠ α in 𝓝[>] 1, |(α - 1) * r α| ≤ 1 :=
      h_eps.eventually (Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 one_pos)
        fun x hx => by simpa [Real.dist_0_eq_abs] using hx)
    filter_upwards [self_mem_nhdsWithin, h_small] with α (hα : 1 < α) h_abs
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(ρ‖σ) := sandwichedTraceFunctional_pos ρ σ hker
    have h_log : Real.log (Q̃_ α(ρ‖σ)) = (α - 1) * r α := by
      simp only [hr_def]
      field_simp
    have h_exp : Q̃_ α(ρ‖σ) = Real.exp ((α - 1) * r α) := by
      rw [← h_log, Real.exp_log hQ_pos]
    have h_bound : Q̃_ α(ρ‖σ) - 1 ≤ (α - 1) * r α + ((α - 1) * r α) ^ 2 := by
      have h₂ := Real.abs_exp_sub_one_sub_id_le h_abs
      have h₃ := le_abs_self (Real.exp ((α - 1) * r α) - 1 - (α - 1) * r α)
      rw [h_exp]
      linarith
    calc (Q̃_ α(ρ‖σ) - 1) / (α - 1)
        ≤ ((α - 1) * r α + ((α - 1) * r α) ^ 2) / (α - 1) :=
          div_le_div_of_nonneg_right h_bound hα1.le
      _ = r α + ((α - 1) * r α) * r α := by
          field_simp

/-- A binary `Mixable` mixture of states, written as a weighted sum of matrices over
`Fin 2` — the form consumed by `sandwichedTraceFunctional_jointly_convex` and
`HermitianMat.ker_weighted_sum_le`. -/
private lemma mix_M_eq_weighted_sum (p : Prob) (τ₁ τ₂ : MState d) :
    (p [τ₁ ↔ τ₂]).M = ∑ i, ![(p : ℝ), 1 - (p : ℝ)] i • (![τ₁, τ₂] i).M := by
  simp only [Mixable.mix, Mixable.mix_ab, MState.instMixable, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Prob.coe_one_minus]
  rfl

/-- A binary mixture preserves the support condition (kernel inclusion) of its
components. -/
private lemma ker_mix_le (p : Prob) {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := by
  rw [mix_M_eq_weighted_sum, mix_M_eq_weighted_sum]
  exact HermitianMat.ker_weighted_sum_le _
    (by intro i; fin_cases i <;> simp) _ _
    (fun i => (![ρ₁, ρ₂] i).nonneg) (fun i => (![σ₁, σ₂] i).nonneg)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Binary case of the joint convexity of the trace functional `Q̃_α` for `α > 1`
(`sandwichedTraceFunctional_jointly_convex`), stated for a `Mixable` mixture. -/
private lemma sandwichedTraceFunctional_mix_le (hα : 1 < α) (p : Prob)
    {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      (p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂) := by
  simpa [Fin.sum_univ_two] using sandwichedTraceFunctional_jointly_convex hα
    ![(p : ℝ), 1 - (p : ℝ)]
    (by intro i; fin_cases i <;> simp)
    (by simp [Fin.sum_univ_two]) ![ρ₁, ρ₂] ![σ₁, σ₂]
    (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
    (mix_M_eq_weighted_sum p ρ₁ ρ₂) (mix_M_eq_weighted_sum p σ₁ σ₂)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Joint convexity of the quantum relative entropy.

This is stated using `Mixable`, rather than `ConvexOn`, because `MState d`
is not an `AddCommMonoid`.
-/
theorem qRelativeEnt_joint_convexity :
    ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
      𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  intro ρ₁ ρ₂ σ₁ σ₂ p
  -- Degenerate mixing weights: the mixture is just one of the two pairs.
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  have hp0' : (0 : ℝ) < p := Prob.zero_lt_coe hp0
  have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne Prob.coe_le_one fun h => hp1 (Subtype.ext h)
  -- If either relative entropy on the right is `⊤`, the bound is trivial.
  by_cases hker₁ : σ₁.M.ker ≤ ρ₁.M.ker
  swap
  · have h_ne : ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, Prob.ofNNReal_toNNReal, ENNReal.ofReal_eq_zero]
      exact not_le.mpr hp0'
    rw [qRelativeEnt_eq_top_iff.mpr hker₁, ENNReal.mul_top h_ne, top_add]
    exact le_top
  by_cases hker₂ : σ₂.M.ker ≤ ρ₂.M.ker
  swap
  · have h_ne : (1 : ENNReal) - ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, tsub_eq_zero_iff_le, Prob.ofNNReal_toNNReal, not_le,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp0'.le |>.mpr hp1'
    rw [qRelativeEnt_eq_top_iff.mpr hker₂, ENNReal.mul_top h_ne, add_top]
    exact le_top
  -- Main case: `0 < p < 1` and both kernel conditions hold, so both `𝐃`s are finite.
  obtain ⟨u₁, hu₁, hb₁⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₁ σ₁ hker₁
  obtain ⟨u₂, hu₂, hb₂⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₂ σ₂ hker₂
  have hker_mix : (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := ker_mix_le p hker₁ hker₂
  -- As `α → 1⁺`, `D̃_α` of the mixture tends to `𝐃` of the mixture...
  have h_lhs := sandwichedRelRentropy_tendsto_qRelativeEnt (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
  -- ...and the convex combination of the majorants tends to the convex combination of the `𝐃`s.
  have h_rhs : Filter.Tendsto
      (fun α : ℝ => ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α)) (𝓝[>] 1)
      (𝓝 (p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂))) := by
    -- The limit is the `ENNReal`-valued convex combination of the two finite `𝐃`s,
    -- rewritten via `ofReal` of the corresponding real combination.
    have h_id : ENNReal.ofReal ((p : ℝ) * (𝐃(ρ₁‖σ₁)).toReal
        + (1 - (p : ℝ)) * (𝐃(ρ₂‖σ₂)).toReal) = p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
      have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by simp
      rw [ENNReal.ofReal_add (mul_nonneg p.zero_le_coe ENNReal.toReal_nonneg)
          (mul_nonneg h1p ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul p.zero_le_coe, ENNReal.ofReal_mul h1p,
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₁),
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₂),
        ENNReal.ofReal_sub 1 p.zero_le_coe, ENNReal.ofReal_one]
      simp only [← Prob.ofNNReal_toNNReal]
    rw [← h_id]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hu₁.const_mul (p : ℝ)).add (hu₂.const_mul (1 - (p : ℝ))))
  -- The pointwise bound for `α > 1`, from joint convexity of `Q̃_α` and `log x ≤ x - 1`.
  have h_ev : ∀ᶠ α in 𝓝[>] 1, D̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α) := by
    filter_upwards [self_mem_nhdsWithin, hb₁, hb₂] with α (hα : 1 < α) h₁ h₂
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) :=
      sandwichedTraceFunctional_pos _ _ hker_mix
    rw [sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker_mix]
    apply ENNReal.ofReal_le_ofReal
    calc Real.log (Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂])) / (α - 1)
        ≤ (((p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂)) - 1) / (α - 1) :=
          div_le_div_of_nonneg_right ((Real.log_le_sub_one_of_pos hQ_pos).trans
            (sub_le_sub_right (sandwichedTraceFunctional_mix_le hα p hker₁ hker₂) 1)) hα1.le
      _ = (p : ℝ) * ((Q̃_ α(ρ₁‖σ₁) - 1) / (α - 1)) +
          (1 - (p : ℝ)) * ((Q̃_ α(ρ₂‖σ₂) - 1) / (α - 1)) := by
          field_simp
          ring
      _ ≤ (p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ hp0'.le)
            (mul_le_mul_of_nonneg_left h₂ (by linarith))
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ev
