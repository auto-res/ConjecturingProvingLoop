

theorem Topology.P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense A) (hAB : (A : Set X) ⊆ B) : Topology.P3 B := by
  dsimp [Topology.P3]
  intro x hxB
  -- Show that `closure B = univ`.
  have hsub : (Set.univ : Set X) ⊆ closure B := by
    intro y _
    -- Since `closure A = univ`, every point lies in `closure A`.
    have hyA : y ∈ closure A := by
      simpa [hA.closure_eq] using (by simp : y ∈ (Set.univ : Set X))
    -- Monotonicity of `closure` upgrades the membership.
    have hcl : closure A ⊆ closure B := closure_mono hAB
    exact hcl hyA
  have hclosureB : closure B = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; simp
    · exact hsub
  -- Conclude the goal using the computed equality.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hclosureB, interior_univ] using this