

theorem P3_iff_nhds_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, closure A ∈ 𝓝 x := by
  refine ⟨?forward, ?backward⟩
  · intro hP3 x hx
    -- From `P3` we know that `x ∈ interior (closure A)`.
    have hx_int : x ∈ interior (closure A) := hP3 hx
    -- The interior is open, hence a neighbourhood of `x`.
    have h_nhds_int : (interior (closure A) : Set X) ∈ 𝓝 x :=
      (isOpen_interior : IsOpen (interior (closure A))).mem_nhds hx_int
    -- Any superset of a neighbourhood is again a neighbourhood.
    exact Filter.mem_of_superset h_nhds_int interior_subset
  · intro h x hx
    -- We are given that `closure A` is a neighbourhood of `x`.
    have h_nhds_cl : (closure A : Set X) ∈ 𝓝 x := h x hx
    -- Unpack the neighbourhood condition to obtain an open set `U`
    -- with `x ∈ U ⊆ closure A`.
    rcases mem_nhds_iff.1 h_nhds_cl with ⟨U, hU_sub, hU_open, hxU⟩
    -- Since `U` is open and contained in `closure A`, it is contained
    -- in `interior (closure A)`.
    have hU_int : (U : Set X) ⊆ interior (closure A) :=
      interior_maximal hU_sub hU_open
    -- Therefore `x ∈ interior (closure A)`.
    exact hU_int hxU

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P2 (Set.prod A B)) : P2 (Set.prod B A) := by
  -- Let `e` be the coordinate-swap homeomorphism.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)

  -- Transport `P2` along `e`.
  have h_image : P2 (e '' (Set.prod A B)) :=
    P2_image_homeomorph (e := e) (A := Set.prod A B) h

  -- Identify the image of `A ×ˢ B` under `e`.
  have h_eq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · -- `→`
      rintro ⟨q, hq, rfl⟩
      rcases q with ⟨a, b⟩
      rcases hq with ⟨ha, hb⟩
      -- After swapping we are at `(b, a)`.
      simpa [e] using And.intro hb ha
    · -- `←`
      intro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, ?_⟩
      · simpa using And.intro ha hb
      · simp [e]

  -- Prove `P2` for `B ×ˢ A`.
  intro p hp
  -- Regard `p` as an element of the image set.
  have hp_image : p ∈ (e '' (Set.prod A B)) := by
    simpa [h_eq] using hp
  -- Apply the transported `P2` and rewrite back using `h_eq`.
  have hp_int := h_image hp_image
  simpa [h_eq] using hp_int

theorem P3_sigma_subtype {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 {x : X | ∃ i, x ∈ A i} := by
  -- First obtain `P3` for the union `⋃ i, A i`.
  have hP3_union : P3 (⋃ i, A i) := P3_Unionᵢ (A := A) h
  -- Show that the set of elements belonging to some `A i` coincides with the union.
  have h_eq : ({x : X | ∃ i, x ∈ A i} : Set X) = ⋃ i, A i := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
  -- Transfer `P3` along the above equality.
  intro x hx
  -- View `x` as an element of the union.
  have hx_union : (x : X) ∈ ⋃ i, A i := by
    simpa [h_eq] using hx
  -- Apply `P3` for the union.
  have hx_int : (x : X) ∈ interior (closure (⋃ i, A i)) :=
    hP3_union hx_union
  -- Rewrite back using the equality.
  simpa [h_eq] using hx_int

theorem P3_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P3 (A ∪ interior A) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_int_clA : x ∈ interior (closure A) := hA hxA
      -- `closure A ⊆ closure (A ∪ interior A)`
      have h_closure :
          (closure A : Set X) ⊆ closure (A ∪ interior A) := by
        have h_sub : (A : Set X) ⊆ A ∪ interior A := by
          intro y hy
          exact Or.inl hy
        exact closure_mono h_sub
      -- hence the desired inclusion on interiors
      have h_subset :
          (interior (closure A) : Set X) ⊆
            interior (closure (A ∪ interior A)) :=
        interior_mono h_closure
      exact h_subset hx_int_clA
  | inr hx_intA =>
      -- `x ∈ interior A`
      -- First view `x` as an element of `A`.
      have hxA : x ∈ A := interior_subset hx_intA
      -- Apply `P3` for `A`.
      have hx_int_clA : x ∈ interior (closure A) := hA hxA
      -- `closure A ⊆ closure (A ∪ interior A)`
      have h_closure :
          (closure A : Set X) ⊆ closure (A ∪ interior A) := by
        have h_sub : (A : Set X) ⊆ A ∪ interior A := by
          intro y hy
          exact Or.inl hy
        exact closure_mono h_sub
      -- hence the desired inclusion on interiors
      have h_subset :
          (interior (closure A) : Set X) ⊆
            interior (closure (A ∪ interior A)) :=
        interior_mono h_closure
      exact h_subset hx_int_clA