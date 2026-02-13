

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  -- Unfold the definition of `P1` in the hypothesis and the goal.
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`.
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- `closure_mono` applied to `hA`, and then rewrite with `closure_closure`.
    have h := closure_mono (hA : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using h
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- first `interior A ⊆ interior (closure A)`
    have h' : interior (A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- then take closures
    exact closure_mono h'
  -- Chain the inclusions to send `x` to the desired set.
  exact h₂ (h₁ hx)

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at hA ⊢
  -- Take a point of the image.
  intro y hy
  -- Write it as `e x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the hypothesis on `A`.
  have hx : x ∈ closure (interior (A : Set X)) := hA hxA
  -- Transport this membership with `e`.
  have h_mem : (e : X → Y) x ∈ e '' closure (interior (A : Set X)) :=
    ⟨x, hx, rfl⟩
  -- Turn it into a membership in `closure (e '' interior A)`.
  have hx_cl : (e : X → Y) x ∈ closure (e '' interior (A : Set X)) := by
    have h_eq :
        e '' closure (interior (A : Set X)) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (s := interior (A : Set X))
    simpa [h_eq] using h_mem
  -- We now relate the two closures that appear.
  have h_closure_mono :
      closure (e '' interior (A : Set X)) ⊆
        closure (interior (e '' A)) := by
    -- It suffices to show the inclusion without the closures.
    apply closure_mono
    -- Show that `e '' interior A ⊆ interior (e '' A)`.
    have h_sub :
        (e '' interior (A : Set X)) ⊆ interior (e '' A) := by
      -- The left set is open (as `e` is an open map) and contained in `e '' A`.
      have h_open :
          IsOpen (e '' interior (A : Set X)) :=
        (e.isOpenMap) _ isOpen_interior
      apply interior_maximal
      · intro z hz
        rcases hz with ⟨x', hx'int, rfl⟩
        exact ⟨x', interior_subset hx'int, rfl⟩
      · exact h_open
    exact h_sub
  -- Conclude for our point.
  exact h_closure_mono hx_cl

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  -- Unfold the definition of `P2` in the hypothesis and in the goal.
  dsimp [Topology.P2] at hA ⊢
  -- Take a point in the image.
  intro y hy
  -- Write it as `e x` with `x ∈ A`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- Use the hypothesis `hA`.
  have hx : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  -- Consider the open set  `W = e '' interior (closure (interior A))`.
  have hW_open :
      IsOpen (e '' interior (closure (interior (A : Set X)))) :=
    (e.isOpenMap) _ isOpen_interior
  -- Our point belongs to `W`.
  have hxW :
      (e : X → Y) x ∈ e '' interior (closure (interior (A : Set X))) :=
    ⟨x, hx, rfl⟩
  -- We claim that `W ⊆ closure (interior (e '' A))`.
  have hW_sub :
      (e '' interior (closure (interior (A : Set X)))) ⊆
        closure (interior (e '' (A : Set X))) := by
    intro z hz
    rcases hz with ⟨x', hx', rfl⟩
    -- From `hx'` we get `x' ∈ closure (interior A)`.
    have hx'_cl : x' ∈ closure (interior (A : Set X)) :=
      interior_subset hx'
    -- Transport this membership with `e`.
    have hmem :
        (e : X → Y) x' ∈ e '' closure (interior (A : Set X)) :=
      ⟨x', hx'_cl, rfl⟩
    -- Rewrite using `e.image_closure`.
    have h_eq :
        e '' closure (interior (A : Set X)) =
          closure (e '' interior (A : Set X)) := by
      simpa using e.image_closure (s := interior (A : Set X))
    have hz1 :
        (e : X → Y) x' ∈ closure (e '' interior (A : Set X)) := by
      simpa [h_eq] using hmem
    -- Relate the two closures.
    have h_cl_sub :
        closure (e '' interior (A : Set X)) ⊆
          closure (interior (e '' (A : Set X))) := by
      -- First show the inclusion without closures.
      have h_sub :
          (e '' interior (A : Set X)) ⊆ interior (e '' (A : Set X)) := by
        -- The left-hand set is open and contained in `e '' A`.
        have h_open' :
            IsOpen (e '' interior (A : Set X)) :=
          (e.isOpenMap) _ isOpen_interior
        have h_incl :
            (e '' interior (A : Set X)) ⊆ e '' (A : Set X) := by
          intro y hy
          rcases hy with ⟨x0, hx0, rfl⟩
          exact ⟨x0, interior_subset hx0, rfl⟩
        exact interior_maximal h_incl h_open'
      exact closure_mono h_sub
    exact h_cl_sub hz1
  -- Since `W` is open and contained in the closure, it is contained in its interior.
  have hW_sub_int :
      (e '' interior (closure (interior (A : Set X)))) ⊆
        interior (closure (interior (e '' (A : Set X)))) :=
    interior_maximal hW_sub hW_open
  -- Conclude for our point.
  exact hW_sub_int hxW

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (A ∪ B ∪ C) := by
  have hAB : Topology.P3 (A ∪ B) := P3_union (X := X) hA hB
  simpa [Set.union_assoc] using
    (P3_union (X := X) (A := A ∪ B) (B := C) hAB hC)