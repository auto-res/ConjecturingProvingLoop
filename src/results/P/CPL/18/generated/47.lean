

theorem P2_bUnion_closed {X ι : Type*} [TopologicalSpace X] {s : Set ι} {A : ι → Set X} (hA : ∀ i ∈ s, IsClosed (A i)) (hP : ∀ i ∈ s, Topology.P2 (A i)) : Topology.P2 (⋃ i ∈ s, A i) := by
  dsimp [Topology.P2] at hP ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨his, hxAi⟩
  have hP2i : Topology.P2 (A i) := hP i his
  have hx' : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ i ∈ s, A i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    have : y ∈ ⋃ j ∈ s, A j := by
      apply Set.mem_iUnion.2
      exact ⟨i, Set.mem_iUnion.2 ⟨his, hy⟩⟩
    exact this
  exact hsubset hx'

theorem P3_image_open_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Embedding f) (h_open : IsOpenMap f) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (f '' A) := by
  -- Unfold the definition of `P3` in the hypothesis and in the goal.
  dsimp [Topology.P3] at hA ⊢
  -- Take a point of `f '' A`.
  intro y hy
  -- Write it as `f x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis on `A`.
  have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Consider the open set `W = f '' interior (closure A)`.
  have hW_open :
      IsOpen (f '' interior (closure (A : Set X))) :=
    h_open _ isOpen_interior
  -- Our point belongs to `W`.
  have hxW :
      (f : X → Y) x ∈ f '' interior (closure (A : Set X)) :=
    ⟨x, hx_int, rfl⟩
  -- We now show `W ⊆ closure (f '' A)`.
  have hW_sub :
      (f '' interior (closure (A : Set X))) ⊆
        closure (f '' (A : Set X)) := by
    intro z hz
    rcases hz with ⟨x', hx'int, rfl⟩
    -- First, `x' ∈ closure A`.
    have hx'_cl : x' ∈ closure (A : Set X) := interior_subset hx'int
    -- We prove that `f x'` is in the desired closure.
    have : f x' ∈ closure (f '' (A : Set X)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hfxV
      -- Pull the neighbourhood back through `f`.
      have hU_open : IsOpen (f ⁻¹' V) := hVopen.preimage hf.continuous
      have hx'U : x' ∈ f ⁻¹' V := hfxV
      -- Since `x'` is in the closure of `A`, `f ⁻¹' V` meets `A`.
      have h_nonempty :
          ((f ⁻¹' V) ∩ (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hx'_cl _ hU_open hx'U
      rcases h_nonempty with ⟨w, ⟨hwU, hwA⟩⟩
      -- The point `f w` is in `V ∩ f '' A`.
      have hfw_in : f w ∈ V ∩ f '' (A : Set X) := by
        refine And.intro ?_ ?_
        · exact hwU
        · exact ⟨w, hwA, rfl⟩
      -- Provide the required witness.
      exact ⟨f w, hfw_in⟩
    exact this
  -- By maximality of the interior we obtain the desired inclusion.
  have hW_sub_int :
      (f '' interior (closure (A : Set X))) ⊆
        interior (closure (f '' (A : Set X))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P1 B) : Topology.P1 ((Set.univ : Set X).prod B) := by
  have hUniv : Topology.P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)

theorem exists_P1_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · simpa using (P1_empty (X := X))