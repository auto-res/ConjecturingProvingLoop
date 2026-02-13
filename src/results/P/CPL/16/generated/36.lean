

theorem P1_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P1 A) → P1 (⋃₀ 𝒜) := by
  intro h
  apply P1_sUnion
  intro A hA
  exact (h A hA).2

theorem P2_sUnion_closed {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsClosed A ∧ P2 A) → P2 (⋃₀ 𝒜) := by
  intro h
  apply P2_sUnion
  intro A hA
  exact (h A hA).2

theorem P2_prod_same {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (Set.prod A A) ↔ P2 A := by
  constructor
  · intro hProd
    -- We turn `hProd` into a pointwise statement.
    -- Unfold the definition of `P2`.
    unfold P2 at hProd ⊢
    intro x hxA
    -- Apply the hypothesis to the diagonal point `(x, x)`.
    have hxx :
        (x, x) ∈ interior (closure (interior (Set.prod A A))) :=
      hProd ⟨hxA, hxA⟩
    -- The set that appears on the right-hand side is open.
    have hO_open :
        IsOpen (interior (closure (interior (Set.prod A A))) :
          Set (X × X)) :=
      isOpen_interior
    -- Hence it is a neighbourhood of `(x, x)`.
    have hO_nhds :
        (interior (closure (interior (Set.prod A A))) :
          Set (X × X)) ∈ nhds (x, x) :=
      hO_open.mem_nhds hxx
    -- Using the product neighbourhood basis, pick rectangular neighbourhoods.
    rcases (mem_nhds_prod_iff).1 hO_nhds with
      ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
    -- Further shrink these neighbourhoods.
    rcases (mem_nhds_iff).1 hU_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
    rcases (mem_nhds_iff).1 hV_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
    -- Define the open neighbourhood `W := U₀ ∩ V₀` of `x`.
    let W : Set X := U₀ ∩ V₀
    have hW_open : IsOpen (W : Set X) := hU₀_open.inter hV₀_open
    have hxW : x ∈ W := by
      dsimp [W]; exact ⟨hxU₀, hxV₀⟩
    -- First, observe that `U₀ × V₀` is contained in the big open set.
    have hProdSub :
        (Set.prod U₀ V₀ : Set (X × X)) ⊆
          interior (closure (interior (Set.prod A A))) :=
      (Set.prod_mono hU₀_sub hV₀_sub).trans hUV_sub
    -- We show that every point of `W` lies in `closure (interior A)`.
    have hW_subset : (W : Set X) ⊆ closure (interior A) := by
      intro y hyW
      -- The pair `(y, y)` is in the big open set.
      have hyPair :
          (y, y) ∈ interior (closure (interior (Set.prod A A))) := by
        have : (y, y) ∈ (Set.prod U₀ V₀) := by
          exact ⟨hyW.1, hyW.2⟩
        exact hProdSub this
      -- Therefore `(y, y)` is in the closure of `interior (A × A)`.
      have hyPairClos :
          (y, y) ∈ closure (interior (Set.prod A A)) :=
        interior_subset hyPair
      -- Use the characterization of the closure.
      apply (mem_closure_iff).2
      intro S hS hyS
      -- Consider the open set `S × S`.
      have hSS_open : IsOpen (Set.prod S S : Set (X × X)) := hS.prod hS
      have hyPairInSS : (y, y) ∈ Set.prod S S := by
        exact ⟨hyS, hyS⟩
      -- Since `(y, y)` is in the closure, the intersection is non-empty.
      have hNonempty :
          ((Set.prod S S) ∩ interior (Set.prod A A)).Nonempty :=
        (mem_closure_iff).1 hyPairClos _ hSS_open hyPairInSS
      -- Extract a witness `(a, b)`.
      rcases hNonempty with ⟨w, hwSS, hwInt⟩
      rcases w with ⟨a, b⟩
      -- The first coordinate `a` belongs to `S`.
      have haS : a ∈ S := hwSS.1
      -- From `hwInt` we deduce `a ∈ interior A`.
      have haIntA : a ∈ interior A := by
        -- `hwInt` says `(a, b)` is in `interior (A × A)`.
        -- Use neighbourhoods to produce an open set contained in `A`.
        have hInt := hwInt
        have hInt_nhds :
            (interior (Set.prod A A) : Set (X × X)) ∈ nhds (a, b) :=
          isOpen_interior.mem_nhds hInt
        rcases (mem_nhds_prod_iff).1 hInt_nhds with
          ⟨O₁, hO₁_nhds, O₂, hO₂_nhds, hProdSub₂⟩
        rcases (mem_nhds_iff).1 hO₁_nhds with
          ⟨O₁', hO₁'_sub, hO₁'_open, haO₁'⟩
        -- `O₁'` is an open neighbourhood of `a` contained in `A`.
        have hO₁'_subA : (O₁' : Set X) ⊆ A := by
          intro z hz
          have hzO₁ : z ∈ O₁ := hO₁'_sub hz
          have hbO₂ : b ∈ O₂ := mem_of_mem_nhds hO₂_nhds
          have hzPair : (z, b) ∈ Set.prod O₁ O₂ := ⟨hzO₁, hbO₂⟩
          have hzInt : (z, b) ∈ interior (Set.prod A A) := hProdSub₂ hzPair
          have hzProd : (z, b) ∈ Set.prod A A := interior_subset hzInt
          exact hzProd.1
        -- Hence `a` is in `interior A`.
        exact (interior_maximal hO₁'_subA hO₁'_open) haO₁'
      -- `S` meets `interior A`, so `y` is in the closure.
      exact ⟨a, haS, haIntA⟩
    -- `W` is an open neighbourhood of `x` contained in the desired set,
    -- so `x` belongs to the interior.
    have hxInt :
        x ∈ interior (closure (interior A)) :=
      (interior_maximal hW_subset hW_open) hxW
    exact hxInt
  · intro hA
    -- The reverse implication follows from `P2_prod`.
    exact (P2_prod (A := A) (B := A)) hA hA