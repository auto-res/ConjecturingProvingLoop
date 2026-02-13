

theorem closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure (B : Set X) ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We will show `x ∈ closure (A \ B)` via `mem_closure_iff`.
  have : x ∈ closure (A \ B : Set X) := by
    -- Reformulate membership in the closure using open neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Choose an open neighbourhood of `x` that avoids `B`.
    let V : Set X := (closure (B : Set X))ᶜ
    have hVopen : IsOpen V := isClosed_closure.isOpen_compl
    have hxV : x ∈ V := by
      dsimp [V]
      exact hxNotClB
    -- The neighbourhood `U ∩ V` is open, contains `x`, and is disjoint from `B`.
    have hWopen : IsOpen (U ∩ V) := hUopen.inter hVopen
    have hxW : x ∈ U ∩ V := ⟨hxU, hxV⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty : ((U ∩ V) ∩ (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClA
      have h' := h (U ∩ V) hWopen hxW
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h'
    -- Extract a witness `y`.
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyV⟩, hyA⟩⟩
    -- Show that `y ∉ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have hyClB : y ∈ closure (B : Set X) := subset_closure hyB
      have : y ∈ V := hyV
      dsimp [V] at this
      exact this hyClB
    -- Hence `y ∈ U ∩ (A \ B)`, proving the required non‐emptiness.
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  exact this