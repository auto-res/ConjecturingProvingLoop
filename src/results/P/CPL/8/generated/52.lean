

theorem P2_iff_P1_of_regular {X : Type*} [TopologicalSpace X] [T1Space X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior A) → (P2 A ↔ P1 A) := by
  intro hReg
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro _hP1
    intro x hxA
    rcases hReg x hxA with ⟨U, hUopen, hxU, hClosureU⟩
    -- `U` is contained in `closure (interior A)`
    have hUsubset : (U : Set X) ⊆ closure (interior A) := by
      intro y hyU
      have hy_closureU : y ∈ closure U := subset_closure hyU
      have hy_intA : y ∈ interior A := hClosureU hy_closureU
      exact subset_closure hy_intA
    -- hence `x` lies in the interior of that closure
    have : x ∈ interior (closure (interior A)) := by
      have hNhd : (U : Set X) ∈ 𝓝 x := hUopen.mem_nhds hxU
      exact (mem_interior_iff_mem_nhds).2
        (Filter.mem_of_superset hNhd hUsubset)
    exact this

theorem P2_prod_of_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (∅ : Set Y)) := by
  intro _ p hp
  cases hp.2

theorem P1_induction_on_closure {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x, x ∈ closure A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (interior A)) → P1 A := by
  intro h x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  rcases h x hx_cl with ⟨U, _hUopen, hxU, hUsubset⟩
  exact hUsubset hxU

theorem P2_unionᵢ_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (P2_unionᵢ (A := A) hP2)

theorem P2_transfinite_union {X : Type*} [TopologicalSpace X] {ι : Type*} [Preorder ι] {A : ι → Set X} (hmon : ∀ i j, i ≤ j → A i ⊆ A j) : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (P2_unionᵢ (A := A) hP2)