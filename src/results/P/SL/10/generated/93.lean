

theorem Topology.P1_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (U ∩ A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  rcases hx with ⟨hxU, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- First, prove `x ∈ closure (U ∩ interior A)`.
  have hx_cl₂ : x ∈ closure (U ∩ interior A) := by
    -- Use the neighbourhood characterization of the closure.
    have h_mem_closure := (mem_closure_iff).1 hx_cl
    have h_goal : ∀ V, IsOpen V → x ∈ V → (V ∩ (U ∩ interior A)).Nonempty := by
      intro V hV hxV
      -- Intersect the neighbourhood with `U`, which is open and contains `x`.
      have hVU_open : IsOpen (V ∩ U) := hV.inter hU
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- Apply the characterization of `hx_cl`.
      have h_nonempty : (V ∩ U ∩ interior A).Nonempty :=
        h_mem_closure (V ∩ U) hVU_open hxVU
      -- Rearrange the intersection to match the goal.
      simpa [Set.inter_assoc, Set.inter_left_comm] using h_nonempty
    exact (mem_closure_iff).2 h_goal
  -- Next, upgrade to `closure (interior (U ∩ A))` via monotonicity.
  have h_subset : (U ∩ interior A) ⊆ interior (U ∩ A) := by
    have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    have h_sub : (U ∩ interior A) ⊆ U ∩ A := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    exact interior_maximal h_sub h_open
  have hx_final : x ∈ closure (interior (U ∩ A)) := by
    have h_closure_mono : closure (U ∩ interior A) ⊆ closure (interior (U ∩ A)) :=
      closure_mono h_subset
    exact h_closure_mono hx_cl₂
  exact hx_final