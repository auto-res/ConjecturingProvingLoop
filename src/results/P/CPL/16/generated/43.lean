

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · intro h
    exact (P1_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P1_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) ↔ P3 (Set.prod B A) := by
  constructor
  · intro h
    exact (P3_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P3_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P1_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (Set.prod A A) ↔ P1 A := by
  constructor
  · intro hProd
    -- Unfold the definition of `P1`.
    unfold P1 at hProd ⊢
    intro x hxA
    -- From `hProd` we know that `(x,x)` is in the closure of the interior of
    -- `A ×ˢ A`.
    have hx_pair : (x, x) ∈ closure (interior (Set.prod A A)) :=
      hProd ⟨hxA, hxA⟩
    -- Use the neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU hxU
    -- Consider the rectangular neighbourhood `U ×ˢ U` of `(x,x)`.
    have hW_open : IsOpen (Set.prod U U : Set (X × X)) := hU.prod hU
    have hxW : (x, x) ∈ Set.prod U U := by
      exact ⟨hxU, hxU⟩
    -- `U ×ˢ U` meets `interior (A ×ˢ A)`.
    have h_nonempty :
        ((Set.prod U U) ∩ interior (Set.prod A A)).Nonempty :=
      (mem_closure_iff).1 hx_pair _ hW_open hxW
    rcases h_nonempty with ⟨⟨a, b⟩, h_ab_W, h_ab_int⟩
    have haU : a ∈ U := h_ab_W.1
    -- Work in a product neighbourhood of `(a,b)` contained in `A ×ˢ A`.
    have h_int_nhds :
        (interior (Set.prod A A) : Set (X × X)) ∈ nhds (a, b) :=
      isOpen_interior.mem_nhds h_ab_int
    rcases (mem_nhds_prod_iff).1 h_int_nhds with
      ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, h_sub⟩
    rcases (mem_nhds_iff).1 hU₁_nhds with
      ⟨U₂, hU₂_sub, hU₂_open, haU₂⟩
    -- Show that `U₂ ⊆ A`.
    have hU₂_A : (U₂ : Set X) ⊆ A := by
      intro z hz
      have hbV₁ : b ∈ V₁ := mem_of_mem_nhds hV₁_nhds
      have hz_prod : (z, b) ∈ Set.prod U₁ V₁ := ⟨hU₂_sub hz, hbV₁⟩
      have hz_int : (z, b) ∈ interior (Set.prod A A) := h_sub hz_prod
      have hz_prodAA : (z, b) ∈ Set.prod A A :=
        interior_subset hz_int
      exact hz_prodAA.1
    -- Therefore `a ∈ interior A`.
    have ha_intA : a ∈ interior A :=
      (interior_maximal hU₂_A hU₂_open) haU₂
    -- Provide the witness `(a)` for the closure condition.
    exact ⟨a, haU, ha_intA⟩
  · intro hA
    -- Use the already proven `P1_prod`.
    have : P1 (Set.prod A A) := P1_prod (A := A) (B := A) hA hA
    simpa using this

theorem exists_P3_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P3_interior (A := A))