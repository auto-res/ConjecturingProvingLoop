

theorem Set.inter_distrib_right {α : Type*} {s t u : Set α} :
    (t ∪ u) ∩ s = (t ∩ s) ∪ (u ∩ s) := by
  calc
    (t ∪ u) ∩ s = s ∩ (t ∪ u) := by
      simpa [Set.inter_comm]
    _ = (s ∩ t) ∪ (s ∩ u) := by
      simpa using (Set.inter_distrib_left (s := s) (t := t) (u := u))
    _ = (t ∩ s) ∪ (u ∩ s) := by
      simpa [Set.inter_comm, Set.inter_left_comm]