

theorem P1_of_closure_subset_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure A ⊆ interior (closure (interior A)) → Topology.P1 A := by
  intro h
  intro x hxA
  have hx_closureA : (x : X) ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (interior A)) := h hx_closureA
  exact
    (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hx_int

theorem P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ U ⊆ V ∧ V ⊆ closure A := by
  constructor
  · intro hP3
    rcases (P3_iff_exists_open_superset (X := X) (A := A)).1 hP3 with
      ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    exact ⟨U, U, hU_open, hU_open, hA_sub_U, subset_rfl, hU_sub_cl⟩
  · rintro ⟨U, V, hU_open, hV_open, hA_sub_U, hU_sub_V, hV_sub_cl⟩
    have h_exists : ∃ W : Set X, IsOpen W ∧ A ⊆ W ∧ W ⊆ closure A :=
      ⟨V, hV_open, Set.Subset.trans hA_sub_U hU_sub_V, hV_sub_cl⟩
    exact (P3_iff_exists_open_superset (X := X) (A := A)).2 h_exists