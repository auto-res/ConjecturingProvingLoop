

theorem Topology.closure_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A) : Set X).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hCl
    rcases hCl with ⟨x, hxCl⟩
    -- Using the characterization of points in the closure with the open set `univ`.
    have hInt : ((Set.univ : Set X) ∩ A).Nonempty := by
      have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
      have hxU : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact (mem_closure_iff).1 hxCl (Set.univ) hOpen hxU
    rcases hInt with ⟨y, ⟨_, hyA⟩⟩
    exact ⟨y, hyA⟩
  · rintro ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩