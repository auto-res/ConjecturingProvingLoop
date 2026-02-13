

theorem P1_setdiff {X} [TopologicalSpace X] {A B : Set X} : P1 A → IsClosed B → B ⊆ A → P1 (A \ B) := by
  intro hP1 hBclosed hBsub
  intro x hxDiff
  -- Decompose the membership information of `x`.
  rcases hxDiff with ⟨hxA, hxNotB⟩
  -- We will prove that every neighbourhood of `x` meets `interior (A \ B)`.
  have h_closure : x ∈ closure (interior (A \ B)) := by
    -- Use the neighbourhood characterization of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Shrink `U` so that it avoids `B`.
    have hVopen : IsOpen (U ∩ (Bᶜ : Set X)) := hUopen.inter hBclosed.isOpen_compl
    have hxV : x ∈ U ∩ (Bᶜ : Set X) := by
      exact ⟨hxU, hxNotB⟩
    -- From `P1 A`, every neighbourhood of `x` meets `interior A`.
    have hP1_prop :=
      (mem_closure_iff).1 (hP1 hxA)
    -- Hence the shrunken neighbourhood meets `interior A`.
    rcases hP1_prop (U ∩ (Bᶜ : Set X)) hVopen hxV with
      ⟨y, ⟨hyV, hyIntA⟩⟩
    -- `y` lies in `U`.
    have hyU : y ∈ U := hyV.1
    -- `y` avoids `B`.
    have hyNotB : y ∈ (Bᶜ : Set X) := hyV.2
    ----------------------------------------------------------------
    -- Show that `y ∈ interior (A \ B)`.
    ----------------------------------------------------------------
    -- First, observe that `interior A ∩ Bᶜ` is open and contained in `A \ B`.
    have hOpen : IsOpen (interior A ∩ (Bᶜ : Set X)) :=
      isOpen_interior.inter hBclosed.isOpen_compl
    have hSub : (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
      intro z hz; exact ⟨interior_subset hz.1, hz.2⟩
    -- By maximality of the interior, this open set lies in `interior (A \ B)`.
    have hSubsetInt :
        (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ interior (A \ B) :=
      interior_maximal hSub hOpen
    -- Consequently, `y` belongs to `interior (A \ B)`.
    have hyIntDiff : y ∈ interior (A \ B) :=
      hSubsetInt ⟨hyIntA, hyNotB⟩
    -- Provide the required witness that `U` meets `interior (A \ B)`.
    exact ⟨y, ⟨hyU, hyIntDiff⟩⟩
  -- Finish the proof.
  exact h_closure

theorem P1_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  simpa using
    P1_prod (A := A ×ˢ B) (B := C)
      (P1_prod (A := A) (B := B) hA hB) hC

theorem P2_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  have hAB : P2 (A ×ˢ B) := P2_prod (A := A) (B := B) hA hB
  simpa using (P2_prod (A := A ×ˢ B) (B := C) hAB hC)