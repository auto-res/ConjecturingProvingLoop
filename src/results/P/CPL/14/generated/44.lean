

theorem P2_iff_exists_open_nbhd {X} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (closure (interior A)) := by
  unfold P2
  constructor
  · intro hP2 x hxA
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    exact ⟨interior (closure (interior A)), isOpen_interior, hx, subset_rfl⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, _hUopen, hxU, hUsubset⟩
    exact hUsubset hxU

theorem P1_iterate {X} [TopologicalSpace X] {A : Set X} : P1 (closure (interior (closure (interior A)))) := by
  -- Unfold the definition of `P1`.
  intro x hx
  ----------------------------------------------------------------
  -- 1.  `interior (closure (interior A))` is open and contained in its
  --     own closure, hence it lies in the interior of that closure.
  ----------------------------------------------------------------
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (closure (interior A)))) := by
    -- `interior (closure (interior A))` is open.
    have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
    -- It is, of course, contained in its closure.
    have h_le :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior A))) :=
      subset_closure
    -- Therefore it is contained in the interior of that closure.
    exact interior_maximal h_le h_open
  ----------------------------------------------------------------
  -- 2.  Taking closures yields the inclusion we need for `P1`.
  ----------------------------------------------------------------
  have h_closure :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure (interior (closure (interior A))))) :=
    closure_mono h_subset
  ----------------------------------------------------------------
  -- 3.  Apply the inclusion to the given point `x`.
  ----------------------------------------------------------------
  exact h_closure hx

theorem P2_homeomorph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (e '' A) := by
  classical
  ----------------------------------------------------------------
  -- A fundamental equality: the homeomorphism transports the `P2`
  -- neighbourhood in the expected way.
  ----------------------------------------------------------------
  have hImageEq :
      (e '' interior (closure (interior A)) : Set Y) =
        interior (closure (interior (e '' A))) := by
    calc
      e '' interior (closure (interior A))
          = interior (e '' closure (interior A)) := by
              simpa using e.image_interior (s := closure (interior A))
      _   = interior (closure (e '' interior A)) := by
              simpa [e.image_closure (s := interior A)]
      _   = interior (closure (interior (e '' A))) := by
              simpa [e.image_interior (s := A)]
  ----------------------------------------------------------------
  -- Forward direction: `P2 A → P2 (e '' A)`.
  ----------------------------------------------------------------
  have forward : P2 A → P2 (e '' A) := by
    intro hP2
    intro y hy
    -- pick a preimage point
    rcases hy with ⟨x, hxA, rfl⟩
    -- apply `P2` for `A`
    have hx : x ∈ interior (closure (interior A)) := hP2 hxA
    -- transport through `e`
    have h_mem : e x ∈ e '' interior (closure (interior A)) := ⟨x, hx, rfl⟩
    -- rewrite via the equality `hImageEq`
    simpa [hImageEq] using h_mem
  ----------------------------------------------------------------
  -- Backward direction: `P2 (e '' A) → P2 A`.
  ----------------------------------------------------------------
  have backward : P2 (e '' A) → P2 A := by
    intro hP2img
    intro x hxA
    -- apply `P2` for the image set
    have hy : e x ∈ interior (closure (interior (e '' A))) :=
      hP2img ⟨x, hxA, rfl⟩
    -- rewrite via `hImageEq`
    have hy' : e x ∈ e '' interior (closure (interior A)) := by
      simpa [hImageEq] using hy
    -- unpack the image–membership and use injectivity
    rcases hy' with ⟨x', hx'int, hx'eq⟩
    have hx_eq : x' = x := by
      apply e.injective
      simpa using hx'eq
    simpa [hx_eq] using hx'int
  ----------------------------------------------------------------
  -- Assemble the equivalence.
  ----------------------------------------------------------------
  exact ⟨forward, backward⟩