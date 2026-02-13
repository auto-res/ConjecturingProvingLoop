

theorem P1_iff_P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ↔ Topology.P2 (Set.univ : Set X) := by
  have hAll := Topology.univ_has_all_Ps (X := X)
  rcases hAll with ⟨hP1, hP2, _⟩
  exact ⟨fun _ => hP2, fun _ => hP1⟩