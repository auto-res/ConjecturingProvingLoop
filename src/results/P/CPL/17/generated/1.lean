

theorem P1_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hPA hPB
  intro x hx
  cases hx with
  | inl hxA =>
      -- x ∈ A
      have hx_closureA : x ∈ closure (interior A) := hPA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsub_interior : interior A ⊆ interior (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h
        exact closure_mono hsub_interior
      exact hsubset hx_closureA
  | inr hxB =>
      -- x ∈ B
      have hx_closureB : x ∈ closure (interior B) := hPB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsub_interior : interior B ⊆ interior (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h
        exact closure_mono hsub_interior
      exact hsubset hx_closureB

theorem exists_open_between_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  intro _ hP3
  exact (P3_iff_exists_open_superset (X := X) (A := A)).1 hP3

theorem P2_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_in
  | inr hxB =>
      have hx_in : x ∈ interior (closure (interior B)) := hP2B hxB
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_in