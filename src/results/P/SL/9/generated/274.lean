

theorem Topology.frontier_inter_self_eq_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ∩ A = A \ interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hfront, hA⟩
    exact ⟨hA, hfront.2⟩
  · intro hx
    rcases hx with ⟨hA, h_not_int⟩
    have h_cl : x ∈ closure (A : Set X) := subset_closure hA
    have h_front : x ∈ frontier (A : Set X) := ⟨h_cl, h_not_int⟩
    exact ⟨h_front, hA⟩