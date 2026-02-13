

theorem P2_implies_P3 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := h hxA
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_int_subset hxInt

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 A := by
  dsimp [Topology.P2, Topology.P1] at *
  exact subset_trans h interior_subset

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 A ∧ Topology.P3 A := by
  exact ⟨Topology.P2_implies_P1 h, Topology.P2_implies_P3 h⟩

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) ↔ Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  simpa [hA.interior_eq]

theorem Topology.P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hxA
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  exact subset_closure hxInt

theorem Set.subset_closure {X : Type*} [TopologicalSpace X] {s : Set X} :
    s ⊆ closure s := by
  intro x hx
  have h : ∀ o : Set X, IsOpen o → x ∈ o → (o ∩ s).Nonempty := by
    intro o ho hxo
    exact ⟨x, hxo, hx⟩
  exact (mem_closure_iff).2 h

theorem Topology.P1_iff_closureInterior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    have h₁ : A ⊆ closure (interior A) := hP1
    have h₂ : closure (interior A) ⊆ A := by
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using this
    exact subset_antisymm h₂ h₁
  · intro hEq
    simpa [Topology.P1, hEq] using (subset_rfl : A ⊆ A)

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (A := A) ↔ IsOpen A := by
  dsimp [Topology.P3] at *
  have h_closure_eq : closure A = A := hA_closed.closure_eq
  constructor
  · intro hP3
    -- Rewrite using the fact that `closure A = A`.
    have h_subset : A ⊆ interior A := by
      simpa [h_closure_eq] using hP3
    -- `interior A` is always a subset of `A`.
    have h_subset' : interior A ⊆ A := interior_subset
    -- Hence `interior A = A`.
    have h_eq : interior A = A := subset_antisymm h_subset' h_subset
    -- An interior is open, and equality gives the desired openness of `A`.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    -- Since `A` is open, it is contained in its own interior.
    have h1 : A ⊆ interior A := by
      simpa [hA_open.interior_eq] using (subset_rfl : A ⊆ A)
    -- The interior is monotone with respect to set inclusion.
    have h2 : interior A ⊆ interior (closure A) :=
      interior_mono subset_closure
    -- Combining the two inclusions yields the desired result.
    exact subset_trans h1 h2

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  simpa [hA.closure_eq] using (Set.mem_univ x)

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  have hxIntA : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hxIntA

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) := by
  dsimp [Topology.P2]
  intro x hxA
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa [hA.interior_eq] using h_subset hxA

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    Topology.P1 (A := A) := by
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact Topology.P1_of_isOpen (A := A) hA_open

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (A := A) ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  · intro hA_open
    exact Topology.P2_of_isOpen (A := A) hA_open

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro _; exact Topology.P2_of_isOpen (A := A) hA
  · intro _; exact Topology.P1_of_isOpen (A := A) hA

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  have h1 := Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 := Topology.P2_iff_P3_of_isOpen (A := A) hA
  exact h1.trans h2

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (A := interior A) := by
  exact Topology.P2_of_isOpen (A := interior A) isOpen_interior

theorem Topology.subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    A ⊆ closure A := by
  exact Set.subset_closure

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have hx' : x ∈ closure (interior A) := Set.subset_closure hx
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa [h_open.interior_eq] using hx'

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  have h1 := (Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed)
  have h2 := (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed)
  exact h1.trans h2.symm

theorem Topology.P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  exact
    ⟨Topology.P1_of_isOpen (A := A) hA,
     Topology.P2_of_isOpen (A := A) hA,
     Topology.P3_of_isOpen (A := A) hA⟩

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (A := interior A) := by
  exact Topology.P3_of_isOpen (A := interior A) isOpen_interior

theorem Topology.closureInterior_subset_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact closure_mono h

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (A := interior (closure A)) := by
  exact Topology.P2_of_isOpen (A := interior (closure A)) isOpen_interior

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (A := interior (closure A)) := by
  exact Topology.P3_of_isOpen (A := interior (closure A)) isOpen_interior

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior (closure A)) := Set.subset_closure hx
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa [h_open.interior_eq] using this

theorem Topology.P1_iff_closureInterior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A := A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    -- `closure (interior A)` is always contained in `closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- From `P1`, we also have the reverse inclusion after taking closures.
    have h₂ : closure A ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [closure_closure] using closure_mono hA
    exact subset_antisymm h₁ h₂
  · intro hEq
    dsimp [Topology.P1]
    intro x hxA
    have hx_closure : x ∈ closure A := Set.subset_closure hxA
    simpa [hEq] using hx_closure

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) : Topology.P1 (A := closure A) := by
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hx_closureA
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_closure_subset hx_closureA

theorem Topology.P1_P2_P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  have hA_open : IsOpen A := by
    simpa using isOpen_discrete A
  exact Topology.P1_P2_P3_of_isOpen (A := A) hA_open

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) : Topology.P1 (A := closure A) := by
  have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
  exact Topology.P3_implies_P1_closure (A := A) hP3

theorem Topology.closureInterior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  have hP1 : Topology.P1 (A := A) := Topology.P1_of_isOpen (A := A) hA
  simpa using (Topology.P1_iff_closureInterior_eq_closure (A := A)).1 hP1

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) :
    Topology.P1 (A := A ∪ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_subset' : A ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_subset'
        exact closure_mono h_int_subset
      exact h_subset hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_subset' : B ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_subset'
        exact closure_mono h_int_subset
      exact h_subset hx_closure

theorem closure_diff_subset {X : Type*} [TopologicalSpace X] (s t : Set X) :
    closure (s \ t) ⊆ closure s \ interior t := by
  intro x hx
  -- `x` lies in the closure of `s`
  have hx_cl_s : x ∈ closure s := by
    have h_sub : s \ t ⊆ s := by
      intro y hy
      exact hy.1
    exact closure_mono h_sub hx
  -- `x` is not in the interior of `t`
  have hx_not_int : x ∉ interior t := by
    by_contra hx_int
    -- Any neighbourhood of `x` meets `s \\ t`; pick `interior t`
    have h_nonempty : ((interior t) ∩ (s \ t)).Nonempty := by
      have h_closure := (mem_closure_iff).1 hx
      exact h_closure _ isOpen_interior hx_int
    rcases h_nonempty with ⟨y, ⟨hy_int_t, hy_diff⟩⟩
    have : y ∈ t := interior_subset hy_int_t
    exact hy_diff.2 this
  exact ⟨hx_cl_s, hx_not_int⟩

theorem Topology.P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    Topology.P2 (A := A) := by
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact Topology.P2_of_isOpen (A := A) hA_open

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      have hxIntA : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure A ⊆ closure (A ∪ B) := by
          have hA_subset : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact closure_mono hA_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntA
  | inr hxB =>
      have hxIntB : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure_subset : closure B ⊆ closure (A ∪ B) := by
          have hB_subset : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact closure_mono hB_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntB

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Dense (A : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  simpa [hA.closure_eq] using
    (by
      simp : interior (Set.univ : Set X) = (Set.univ : Set X))

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hxAB
  cases hxAB with
  | inl hxA =>
      -- Use `P2` on `A`
      have hxIntA : x ∈ interior (closure (interior A)) := hA hxA
      -- Show this interior is contained in the desired one
      have h_subset : interior (closure (interior A)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        -- Monotonicity of `interior` and `closure`
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_sub
        have h_closure_subset : closure (interior A) ⊆
                                closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntA
  | inr hxB =>
      -- Symmetric case for `B`
      have hxIntB : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact interior_mono h_sub
        have h_closure_subset : closure (interior B) ⊆
                                closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        exact interior_mono h_closure_subset
      exact h_subset hxIntB

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- Let `S = interior (closure (interior A))`.
  set S : Set X := interior (closure (interior A)) with hS_def
  -- We first show that `closure S ⊆ closure (interior A)`.
  have h_closure_subset : closure S ⊆ closure (interior A) := by
    -- Since `S ⊆ closure (interior A)`, taking closures yields the claim.
    have h_S_subset : S ⊆ closure (interior A) := by
      dsimp [S] at *
      exact interior_subset
    simpa [closure_closure] using closure_mono h_S_subset
  -- From the previous inclusion we get `interior (closure S) ⊆ S`.
  have h_int_subset : interior (closure S) ⊆ S := by
    have h := interior_mono h_closure_subset
    simpa [hS_def] using h
  -- Because `S` is open and `S ⊆ closure S`, we have `S ⊆ interior (closure S)`.
  have h_subset_int : S ⊆ interior (closure S) := by
    have h_open : IsOpen S := by
      dsimp [S]; exact isOpen_interior
    have h_sub : S ⊆ closure S := subset_closure
    exact interior_maximal h_sub h_open
  -- Combine the two inclusions to obtain equality.
  have h_eq : interior (closure S) = S := subset_antisymm h_int_subset h_subset_int
  simpa [hS_def] using h_eq

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (A := (∅ : Set X)) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem Topology.P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) : Topology.P1 (A := closure A) := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx_closureA
  -- First, use `hP1` to see that `closure A ⊆ closure (interior A)`.
  have h₁ : closure A ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using this
  -- Next, note that `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have : interior A ⊆ interior (closure A) := interior_mono subset_closure
    exact closure_mono this
  -- Chain the inclusions to reach the desired membership.
  exact h₂ (h₁ hx_closureA)

theorem Topology.closureInterior_closure_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (A := A)) :
    closure (interior (closure A)) = closure A := by
  -- First, obtain `P1` for `closure A`.
  have hP1_closure : Topology.P1 (A := closure A) :=
    Topology.P1_implies_P1_closure (A := A) hP1
  -- Translate `P1` into the desired equality.
  simpa using
    (Topology.P1_iff_closureInterior_eq_closure (A := closure A)).1 hP1_closure

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (A := closure A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  have hx_closure : x ∈ closure A := Set.subset_closure hxA
  have hx_int : x ∈ interior (closure (closure A)) := h hx_closure
  simpa [closure_closure] using hx_int

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (∅ : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- Let `S = interior (closure A)`.
  set S : Set X := interior (closure A) with hS_def
  -- `closure S` is contained in `closure A`.
  have h_closure_subset : closure S ⊆ closure A := by
    -- Since `S ⊆ closure A`, taking closures yields the inclusion.
    have hS_subset : S ⊆ closure A := by
      dsimp [S] at *
      exact interior_subset
    simpa [closure_closure, hS_def] using closure_mono hS_subset
  -- Hence `interior (closure S) ⊆ S`.
  have h_int_subset : interior (closure S) ⊆ S := by
    have h := interior_mono h_closure_subset
    simpa [hS_def] using h
  -- Because `S` is open, we also have `S ⊆ interior (closure S)`.
  have h_subset_int : S ⊆ interior (closure S) := by
    intro x hxS
    -- `S` is open, so `interior S = S`.
    have h_open : IsOpen S := by
      dsimp [S] at *
      exact isOpen_interior
    have hx_int_S : x ∈ interior S := by
      simpa [h_open.interior_eq] using hxS
    -- Monotonicity of `interior`.
    have h_int_mono : interior S ⊆ interior (closure S) :=
      interior_mono subset_closure
    exact h_int_mono hx_int_S
  -- Combine the inclusions to obtain equality.
  have h_eq : interior (closure S) = S :=
    subset_antisymm h_int_subset h_subset_int
  simpa [hS_def] using h_eq

theorem closure_interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    simpa [closure_closure] using closure_mono h₁
  ·
    have h₂ : interior A ⊆ interior (closure (interior A)) := by
      have h : interior (interior A) ⊆ interior (closure (interior A)) := by
        have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
        exact interior_mono this
      simpa [interior_interior] using h
    simpa [closure_closure] using closure_mono h₂

theorem Topology.interiorClosureInterior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `interior A ⊆ A`.
  have h_subset : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusion, giving
  -- `closure (interior A) ⊆ closure A`.
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono h_subset
  -- Applying monotonicity of `interior` to the previous inclusion
  -- yields the desired result.
  exact interior_mono h_closure

theorem Topology.closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_idempotent (A := closure A))

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (A := (∅ : Set X)) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (Set.univ : Set X)) := by
  dsimp [Topology.P1]
  intro x _
  simp [interior_univ, closure_univ]

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (A := (Set.univ : Set X)) := by
  dsimp [Topology.P2]
  intro x _
  simp [interior_univ, closure_univ]

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_id : closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_idempotent (A := A)
  simpa [h_id] using hx

theorem Topology.P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 (A := A)) (hP3B : Topology.P3 (A := B)) :
    Topology.P3 (A := A ∩ B) := by
  -- From `P3` and closedness, `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3A
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1 hP3B
  -- The intersection of two open sets is open.
  have h_inter_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) h_inter_open

theorem Topology.P2_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A := A ∩ B) := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact Topology.P2_of_isOpen (A := A ∩ B) h_open

theorem Topology.interior_closure_interior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    interior (closure (interior A)) = A := by
  have h_open : IsOpen A := isOpen_discrete _
  have h_closed : IsClosed A := isClosed_discrete _
  simp [h_open.interior_eq, h_closed.closure_eq]

theorem Topology.P1_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A := A ∩ B) := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact Topology.P1_of_isOpen (A := A ∩ B) h_open

theorem Topology.closure_subset_closureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) :
    closure A ⊆ closure (interior A) := by
  -- `P2` implies `P1`, giving `A ⊆ closure (interior A)`.
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hA
  have h_subset : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions.
  simpa [closure_closure] using closure_mono h_subset

theorem Topology.closureInterior_eq_self_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 (A := A)) :
    closure (interior A) = A := by
  -- `P2` implies `P1`.
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hP2
  -- Use the characterisation of `P1` for closed sets.
  exact
    (Topology.P1_iff_closureInterior_eq_of_isClosed (A := A) hA_closed).1 hP1

theorem Topology.interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    interior (closure A) = A := by
  have h_closed : IsClosed A := isClosed_discrete _
  have h_open : IsOpen A := isOpen_discrete _
  have h_closure : closure A = A := h_closed.closure_eq
  simpa [h_closure, h_open.interior_eq]

theorem Topology.P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 (A := A)) (hP2B : Topology.P2 (A := B)) :
    Topology.P2 (A := A ∩ B) := by
  -- From `P2`, derive `P3`, and using closedness convert to openness.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1
      (Topology.P2_implies_P3 hP2A)
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1
      (Topology.P2_implies_P3 hP2B)
  -- The intersection of two open sets is open.
  have h_inter_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A ∩ B) h_inter_open

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (A := (Set.univ : Set X)) := by
  dsimp [Topology.P3]
  intro x _
  simp [closure_univ, interior_univ]

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    interior (closure A) = interior (closure (interior A)) := by
  apply subset_antisymm
  ·
    -- `interior (closure A) ⊆ interior (closure (interior A))`
    have h_subset_closure : closure A ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hA
      simpa [closure_closure] using h'
    exact interior_mono h_subset_closure
  ·
    -- The reverse inclusion holds unconditionally.
    exact Topology.interiorClosureInterior_subset_interiorClosure (A := A)

theorem Topology.P3_inter_of_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P3 (A := A ∩ B) := by
  have h_open : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact Topology.P3_of_isOpen (A := A ∩ B) h_open

theorem Topology.closureInterior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    closure (interior A) = A := by
  have h_open : IsOpen A := isOpen_discrete _
  have h_closed : IsClosed A := isClosed_discrete _
  have h_int : interior A = A := h_open.interior_eq
  have h_closure : closure A = A := h_closed.closure_eq
  simpa [h_int, h_closure]

theorem Topology.interior_closure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA_closed.closure_eq]

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P2 (A := 𝒜 i)) :
    Topology.P2 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P2] at *
  intro x hx_union
  -- Pick an index `i` such that `x ∈ 𝒜 i`.
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  -- Apply `P2` for this particular set.
  have hx_int : x ∈ interior (closure (interior (𝒜 i))) := h𝒜 i hx_i
  -- Show that this interior is contained in the required one.
  have h_subset :
      interior (closure (interior (𝒜 i))) ⊆
        interior (closure (interior (⋃ j, 𝒜 j))) := by
    -- `interior` is monotone with respect to set inclusion.
    have h_int_mono : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_set_subset
    -- Apply monotonicity of `closure` and `interior` successively.
    have h_closure_mono :
        closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) :=
      closure_mono h_int_mono
    exact interior_mono h_closure_mono
  exact h_subset hx_int

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P1 (A := 𝒜 i)) :
    Topology.P1 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P1] at *
  intro x hx_union
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (𝒜 i)) := h𝒜 i hx_i
  have h_subset :
      closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) := by
    have h_int_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_set_subset
    exact closure_mono h_int_subset
  exact h_subset hx_closure

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, Topology.P3 (A := 𝒜 i)) :
    Topology.P3 (A := ⋃ i, 𝒜 i) := by
  dsimp [Topology.P3] at *
  intro x hx_union
  -- Choose an index `i` such that `x ∈ 𝒜 i`.
  rcases Set.mem_iUnion.1 hx_union with ⟨i, hx_i⟩
  -- Apply `P3` for this particular set.
  have hx_int : x ∈ interior (closure (𝒜 i)) := h𝒜 i hx_i
  -- Show this interior is contained in the desired one.
  have h_subset :
      interior (closure (𝒜 i)) ⊆ interior (closure (⋃ j, 𝒜 j)) := by
    -- Monotonicity of `closure`.
    have h_closure_mono :
        closure (𝒜 i) ⊆ closure (⋃ j, 𝒜 j) := by
      have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_set_subset
    -- Apply monotonicity of `interior`.
    exact interior_mono h_closure_mono
  exact h_subset hx_int

theorem Topology.closureInterior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    Topology.P1 (A := A) := by
  exact (Topology.P1_P2_P3_of_discrete (A := A)).1

theorem interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
      simpa using
        (interior_closure_interior_idempotent (A := closure A))
    _ = interior (closure A) := by
      simpa using (interior_closure_idempotent (A := A))

theorem Topology.P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) : Topology.P2 (A := A) := by
  have hA_open : IsOpen A := isOpen_discrete _
  exact Topology.P2_of_isOpen (A := A) hA_open

theorem Topology.closureInterior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    -- `interior (closure A)` is contained in `closure A`, hence their closures relate likewise.
    have h_int_subset : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using closure_mono h_int_subset
  ·
    -- From `P3`, `A ⊆ interior (closure A)`, so taking closures yields the reverse inclusion.
    have h_closure_subset : closure A ⊆ closure (interior (closure A)) := by
      have hA : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [closure_closure] using closure_mono hA
    exact h_closure_subset

theorem Topology.interior_closure_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.closureInteriorClosure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure A)) ⊆ closure A := by
  have h : interior (closure A) ⊆ closure A := interior_subset
  simpa [closure_closure] using closure_mono h

theorem Topology.interiorClosure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) : Topology.P3 (A := A) := by
  exact (Topology.P1_P2_P3_of_discrete (A := A)).2.2

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) :
    interior (closure A) = interior (closure (interior A)) := by
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hP2
  simpa using
    (Topology.interiorClosure_eq_interiorClosureInterior_of_P1
      (A := A) hP1)

theorem Topology.closureInterior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) :
    closure (interior (closure A)) = closure A := by
  have hP3 : Topology.P3 (A := A) := P2_implies_P3 hP2
  exact Topology.closureInterior_closure_eq_closure_of_P3 (A := A) hP3

theorem closure_diff_subset_of_isOpen {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hT : IsOpen t) :
    closure (s \ t) ⊆ closure s \ t := by
  have h := closure_diff_subset (s) (t)
  simpa [hT.interior_eq] using h

theorem Topology.interiorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A := by
      have h_sub : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h_sub
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B := by
      have h_sub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact closure_mono h_sub
    exact (interior_mono h_subset) hx
  exact ⟨hxA, hxB⟩

theorem Topology.closureInteriorInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.P1_iff_P2_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro _; exact Topology.P2_of_discrete (A := A)
  · intro _; exact Topology.P1_of_discrete (A := A)

theorem Topology.interiorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure A ⊆ closure (A ∪ B) := by
        have hA_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono hA_subset
      exact (interior_mono h_subset) hxA
  | inr hxB =>
      have h_subset : closure B ⊆ closure (A ∪ B) := by
        have hB_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono hB_subset
      exact (interior_mono h_subset) hxB

theorem Topology.P1_iff_P3_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  constructor
  · intro _; exact Topology.P3_of_discrete (A := A)
  · intro _; exact Topology.P1_of_discrete (A := A)

theorem Topology.closureInterior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.P2_iff_P3_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  -- Use the equivalences with `P1` already established for discrete spaces.
  have h₁ : Topology.P2 (A := A) ↔ Topology.P1 (A := A) :=
    (Topology.P1_iff_P2_of_discrete (A := A)).symm
  have h₂ : Topology.P1 (A := A) ↔ Topology.P3 (A := A) :=
    Topology.P1_iff_P3_of_discrete (A := A)
  simpa using h₁.trans h₂

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (A := closure A) h_closed)

theorem Topology.closureInterior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A ⊆ interior (A ∪ B)`
      have h_int_subset : interior A ⊆ interior (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono h_subset
      -- Taking closures preserves inclusions.
      have h_closure_subset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxA
  | inr hxB =>
      -- Symmetric argument for `B`.
      have h_int_subset : interior B ⊆ interior (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono h_subset
      have h_closure_subset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_subset
      exact h_closure_subset hxB

theorem Topology.closureInteriorClosureClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  simpa [closure_closure]

theorem Topology.closureInterior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x ∈ closure (interior A)`.
  have hxA : x ∈ closure (interior A) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h_subset : interior (A ∩ B : Set X) ⊆ interior A := by
      -- Since `A ∩ B ⊆ A`, apply monotonicity of `interior`.
      have h_set : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact interior_mono h_set
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
      closure_mono h_subset
    exact h_closure hx
  -- Show `x ∈ closure (interior B)`.
  have hxB : x ∈ closure (interior B) := by
    have h_subset : interior (A ∩ B : Set X) ⊆ interior B := by
      have h_set : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact interior_mono h_set
    have h_closure : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
      closure_mono h_subset
    exact h_closure hx
  exact ⟨hxA, hxB⟩

theorem closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa using
        (closure_interior_closure_interior_idempotent (A := interior A))
    _ = closure (interior A) := by
      simpa using
        (closure_interior_closure_idempotent (A := A))

theorem Topology.P2_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (A := Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.P2_of_isOpen (A := Aᶜ) hA_open

theorem Topology.P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (A := Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.P3_of_isOpen (A := Aᶜ) hA_open

theorem Topology.P1_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P1 (A := Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.P1_of_isOpen (A := Aᶜ) hA_open

theorem Topology.interiorClosure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) ⊆ closure A := by
  simpa using (interior_subset : interior (closure A) ⊆ closure A)

theorem Topology.closure_diff_interior_subset {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A \ interior A) ⊆ closure A \ interior A := by
  simpa using
    (closure_diff_subset_of_isOpen (s := A) (t := interior A) isOpen_interior)

theorem Topology.interiorClosure_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {𝒜 : ι → Set X} :
    interior (closure (⋂ i, 𝒜 i)) ⊆ ⋂ i, interior (closure (𝒜 i)) := by
  intro x hx
  -- Show that `x` lies in every `interior (closure (𝒜 i))`.
  have h_forall : ∀ i, x ∈ interior (closure (𝒜 i)) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, the same holds for their closures.
    have h_subset : closure (⋂ j, 𝒜 j) ⊆ closure (𝒜 i) := by
      have h_inter_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact closure_mono h_inter_subset
    -- Apply monotonicity of `interior`.
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 h_forall

theorem Topology.closureInterior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    closure (interior (⋂ i, 𝒜 i)) ⊆ ⋂ i, closure (interior (𝒜 i)) := by
  intro x hx
  -- Show that `x` lies in every `closure (interior (𝒜 i))`.
  have h_forall : ∀ i, x ∈ closure (interior (𝒜 i)) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, the same holds for their interiors.
    have h_subset : interior (⋂ j, 𝒜 j) ⊆ interior (𝒜 i) := by
      -- The intersection is contained in each component.
      have h_set : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono h_set
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior (⋂ j, 𝒜 j)) ⊆
        closure (interior (𝒜 i)) := closure_mono h_subset
    exact h_closure hx
  exact Set.mem_iInter.2 h_forall

theorem Topology.interior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure



theorem Topology.closureInteriorClosure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  have hP1 : Topology.P1 (A := A) :=
    Topology.P1_of_isOpen (A := A) hA
  simpa using
    (Topology.closureInterior_closure_eq_closure_of_P1 (A := A) hP1)

theorem Topology.closure_compl_subset_compl_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ⊆ (interior A)ᶜ := by
  intro x hx_closure
  -- We must show `x ∉ interior A`.
  intro hx_intA
  -- Use the characterization of closure: every neighbourhood of `x` meets `Aᶜ`.
  have h_nonempty : ((interior A) ∩ Aᶜ).Nonempty := by
    have h_closure := (mem_closure_iff).1 hx_closure
    exact h_closure _ isOpen_interior hx_intA
  -- Derive a contradiction from the non-empty intersection.
  rcases h_nonempty with ⟨y, ⟨hy_int, hy_compl⟩⟩
  have hyA : y ∈ A := interior_subset hy_int
  exact hy_compl hyA

theorem Topology.closureInteriorClosure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, monotonicity of `closure` gives `closure A ⊆ closure B`.
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  -- Applying monotonicity of `interior` yields the next inclusion.
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  -- Finally, use monotonicity of `closure` once more to reach the goal.
  exact closure_mono h_interior

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ) = (interior A)ᶜ := by
  classical
  apply subset_antisymm
  ·
    exact Topology.closure_compl_subset_compl_interior (A := A)
  ·
    intro x hx_not_intA
    have hx_closure : x ∈ closure (Aᶜ) := by
      -- Use the neighborhood characterization of closure.
      have h : ∀ s : Set X, IsOpen s → x ∈ s → (s ∩ Aᶜ).Nonempty := by
        intro s hs hxs
        by_cases h_sub : s ⊆ A
        ·
          -- Then `x ∈ interior A`, contradicting `hx_not_intA`.
          have hx_intA : x ∈ interior A := by
            have h_sub_int : s ⊆ interior A := interior_maximal h_sub hs
            exact h_sub_int hxs
          exact (hx_not_intA hx_intA).elim
        ·
          -- Find a point of `s` outside `A`.
          rcases Set.not_subset.1 h_sub with ⟨y, hy_s, hy_notA⟩
          exact ⟨y, ⟨hy_s, hy_notA⟩⟩
      exact (mem_closure_iff).2 h
    exact hx_closure


theorem subset_univ {α : Type*} {s : Set α} : s ⊆ (Set.univ : Set α) := by
  intro x hx
  trivial

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  classical
  -- Start from the known relation with `Aᶜ`.
  have h := Topology.closure_compl_eq_compl_interior (A := Aᶜ)
  -- `h : closure A = (interior (Aᶜ))ᶜ`
  -- Take complements of both sides.
  have h' := congrArg (fun s : Set X => sᶜ) h
  -- Rearrange and simplify double complements.
  simpa [compl_compl] using h'.symm

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (A := closure A) h_closed)

theorem Topology.closureInteriorCompl_eq_compl_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First, rewrite `interior (Aᶜ)` using the complement–closure relation.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Use `h₁` to rewrite the left‐hand side and then apply the analogous
  -- complement–interior relation to `closure A`.
  calc
    closure (interior (Aᶜ)) = closure ((closure A)ᶜ) := by
      simpa [h₁]
    _ = (interior (closure A))ᶜ := by
      simpa using
        (Topology.closure_compl_eq_compl_interior (A := closure A))

theorem Topology.interiorClosureCompl_eq_compl_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  have h₁ : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  have h₂ : interior ((interior A)ᶜ) = (closure (interior A))ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := interior A)
  simpa [h₁] using h₂

theorem Topology.interiorClosureInterior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- `interior A` is contained in `interior (closure A)`.
  have h_int : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  -- Taking closures preserves this inclusion.
  have h_closure : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int
  -- Applying monotonicity of `interior` once more yields the result.
  exact interior_mono h_closure

theorem Topology.closure_inter_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    -- `A ∩ B ⊆ A`, hence their closures satisfy the same inclusion.
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    have h_closure := closure_mono h_subset
    exact h_closure hx
  have hxB : x ∈ closure B := by
    -- Symmetric argument for `B`.
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy; exact hy.2
    have h_closure := closure_mono h_subset
    exact h_closure hx
  exact ⟨hxA, hxB⟩

theorem Topology.closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    closure (⋂ i, 𝒜 i) ⊆ ⋂ i, closure (𝒜 i) := by
  intro x hx
  -- For each `i`, `⋂ i, 𝒜 i ⊆ 𝒜 i`; taking closures preserves inclusion.
  have h_forall : ∀ i, x ∈ closure (𝒜 i) := by
    intro i
    have h_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 h_forall

theorem Topology.interiorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- `interior` is monotone with respect to set inclusion.
  have h₁ : interior A ⊆ interior B := interior_mono hAB
  -- `closure` preserves inclusions.
  have h₂ : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h₁
  -- Applying monotonicity of `interior` once more yields the desired result.
  exact interior_mono h₂

theorem Topology.closureInterior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (A := A)) :
    closure (interior A) = closure A := by
  exact
    ((Topology.P1_iff_closureInterior_eq_closure (A := A)).1
      (Topology.P2_implies_P1 hP2))

theorem Topology.closureInteriorClosureInteriorClosureInteriorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_interior_closure_interior_idempotent
      (A := closure A))

theorem Topology.interior_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have h_incl : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- `interior A` is open and contained in `closure (interior A)`,
    -- hence it is contained in the interior of that closure.
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    exact interior_maximal h_subset isOpen_interior
  exact h_incl hx

theorem Topology.P1_of_closureInterior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : Topology.P1 (A := A) := by
  dsimp [Topology.P1]
  intro x hxA
  have : x ∈ closure (interior A) := by
    simpa [h] using hxA
  exact this

theorem Topology.interiorClosure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact Set.subset_closure hx

theorem Topology.closureInterior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  simpa [hA.closure_eq] using h

theorem Topology.closure_closureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.interiorClosure_inter_subset_interiorClosureUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  -- It suffices to use the first component `x ∈ interior (closure A)`;
  -- the argument would be symmetric with `closure B`.
  have hxA : x ∈ interior (closure A) := hx.1
  -- `closure A` is contained in `closure (A ∪ B)`.
  have h_subset : closure A ⊆ closure (A ∪ B) := by
    have hA_union : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact closure_mono hA_union
  -- By monotonicity of `interior`, `x` lies in the desired interior.
  exact (interior_mono h_subset) hxA

theorem Topology.iUnion_interiorClosure_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, interior (closure (𝒜 i))) ⊆ interior (closure (⋃ i, 𝒜 i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : closure (𝒜 i) ⊆ closure (⋃ j, 𝒜 j) := by
    have h_set : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono h_set
  exact (interior_mono h_subset) hx_i

theorem Topology.closure_union_subset
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_mono : closure A ⊆ closure (A ∪ B) := by
        have h_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono h_sub
      exact h_mono hA
  | inr hB =>
      have h_mono : closure B ⊆ closure (A ∪ B) := by
        have h_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono h_sub
      exact h_mono hB

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hxA : x ∈ interior (closure (interior A)) := by
    have h_subset : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
      have h_int_subset : interior (A ∩ B : Set X) ⊆ interior A := by
        have h_set : (A ∩ B : Set X) ⊆ A := by
          intro y hy; exact hy.1
        exact interior_mono h_set
      exact closure_mono h_int_subset
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure (interior B)) := by
    have h_subset : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
      have h_int_subset : interior (A ∩ B : Set X) ⊆ interior B := by
        have h_set : (A ∩ B : Set X) ⊆ B := by
          intro y hy; exact hy.2
        exact interior_mono h_set
      exact closure_mono h_int_subset
    exact (interior_mono h_subset) hx
  exact ⟨hxA, hxB⟩



theorem Topology.iUnion_closure_subset_closure_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, closure (𝒜 i)) ⊆ closure (⋃ i, 𝒜 i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_subset : closure (𝒜 i) ⊆ closure (⋃ j, 𝒜 j) :=
    closure_mono h_subset
  exact h_closure_subset hx_i

theorem Topology.disjoint_closureCompl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Disjoint (closure (Aᶜ)) (interior A) := by
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have hsubset : closure (Aᶜ) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  -- Translate this containment into disjointness.
  exact (Set.disjoint_left).2 (by
    intro x hx_cl hx_int
    have : x ∈ (interior A)ᶜ := hsubset hx_cl
    exact this hx_int)

theorem Topology.closure_inter_interiorClosure_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨interior_subset hx, hx⟩

theorem Topology.disjoint_closure_interiorCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (closure A) (interior (Aᶜ)) := by
  simpa [compl_compl] using
    (Topology.disjoint_closureCompl_interior (A := Aᶜ))

theorem Topology.iUnion_closureInterior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, closure (interior (𝒜 i))) ⊆
      closure (interior (⋃ i, 𝒜 i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (𝒜 i)` is contained in `interior (⋃ i, 𝒜 i)`.
  have h_int_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
    have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_set_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure (interior (𝒜 i)) ⊆ closure (interior (⋃ j, 𝒜 j)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_i

theorem Topology.disjoint_closureDiff_interior {X : Type*} [TopologicalSpace X]
    {s t : Set X} :
    Disjoint (closure (s \ t)) (interior t) := by
  -- `closure (s \ t)` is contained in the complement of `interior t`.
  have hsubset : closure (s \ t) ⊆ (interior t)ᶜ := by
    intro x hx
    have hx' : x ∈ closure s \ interior t := (closure_diff_subset s t) hx
    exact hx'.2
  -- Turn this containment into the desired disjointness.
  exact
    (Set.disjoint_left).2 (by
      intro x hx_cl hx_int
      have : x ∈ (interior t)ᶜ := hsubset hx_cl
      exact this hx_int)

theorem Topology.closureInteriorClosure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  calc
    closure (interior (closure A)) = closure (closure A) := by
      simpa [hInt]
    _ = closure A := by
      simpa [closure_closure]

theorem Topology.closure_union_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h_cl : x ∈ closure A
    · exact Or.inl h_cl
    · -- `x ∉ closure A`; we show `x ∈ closure (Aᶜ)`
      have hAcomp : x ∈ Aᶜ := by
        by_cases hA : x ∈ A
        · have : x ∈ closure A := Set.subset_closure hA
          exact (h_cl this).elim
        · simpa [Set.compl_def] using hA
      exact Or.inr (Set.subset_closure hAcomp)

theorem Topology.closure_union_eq {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A ∪ B) = closure A ∪ closure B := by
  apply subset_antisymm
  ·
    -- First, show that `closure (A ∪ B)` is contained in `closure A ∪ closure B`.
    have h_subset : (A ∪ B : Set X) ⊆ closure A ∪ closure B := by
      intro x hx
      cases hx with
      | inl hxA => exact Or.inl (subset_closure hxA)
      | inr hxB => exact Or.inr (subset_closure hxB)
    -- The set on the right is closed, so the minimality of the closure gives the inclusion.
    have h_closed : IsClosed (closure A ∪ closure B) :=
      IsClosed.union isClosed_closure isClosed_closure
    exact closure_minimal h_subset h_closed
  ·
    -- The reverse inclusion is already available.
    exact Topology.closure_union_subset (A) (B)

theorem Topology.closureInterior_isClosed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  -- The closure of any set is closed.
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem Topology.P1_iff_closure_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := A) ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1`, we have `A ⊆ closure (interior A)`.
    -- Taking closures preserves inclusions and yields the desired result.
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono h
  · intro hClosure
    -- To prove `P1`, start with any `x ∈ A`.
    dsimp [Topology.P1] at *
    intro x hxA
    -- Since `A ⊆ closure A`, we first place `x` in `closure A`,
    -- then use the assumed inclusion.
    have hx_closure : x ∈ closure A := Set.subset_closure hxA
    exact hClosure hx_closure

theorem Topology.closureCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ) ∩ interior A = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing that no point belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_closure, hx_int⟩
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have hsubset : closure (Aᶜ : Set X) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  have : x ∈ (interior A)ᶜ := hsubset hx_closure
  exact this hx_int

theorem Topology.isClopen_of_isClosed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    IsClosed A ∧ IsOpen A := by
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact ⟨hA_closed, hA_open⟩

theorem Topology.interior_union_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : x ∈ interior A
    · exact Or.inl hx
    ·
      have hx_comp : x ∈ (interior A)ᶜ := hx
      have h_eq : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
        Topology.closure_compl_eq_compl_interior (A := A)
      have hx_closure : x ∈ closure (Aᶜ) := by
        simpa [h_eq] using hx_comp
      exact Or.inr hx_closure

theorem Topology.closure_diff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A \ interior A) = A \ interior A := by
  -- First, show that `A \ interior A` is closed.
  have h_closed : IsClosed (A \ interior A) := by
    -- The complement of the open set `interior A` is closed.
    have h_compl_closed : IsClosed ((interior A)ᶜ) :=
      (isOpen_interior : IsOpen (interior A)).isClosed_compl
    -- An intersection of two closed sets is closed.
    simpa [Set.diff_eq] using IsClosed.inter hA h_compl_closed
  -- The closure of a closed set is itself.
  simpa [h_closed.closure_eq]

theorem Topology.interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  intro x hx_int
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ A := interior_subset hx_int
  -- Since `A ⊆ closure A`, we conclude `x ∈ closure A`.
  exact subset_closure hxA

theorem Topology.interior_inter_eq_inter
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A ∩ B) = interior A ∩ interior B := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ interior A := by
      have h_subset : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono h_subset) hx
    have hxB : x ∈ interior B := by
      have h_subset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono h_subset) hx
    exact ⟨hxA, hxB⟩
  · intro hx
    have h_open : IsOpen (interior A ∩ interior B) :=
      IsOpen.inter isOpen_interior isOpen_interior
    have h_subset : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨interior_subset hy.1, interior_subset hy.2⟩
    have h_incl : (interior A ∩ interior B : Set X) ⊆
        interior (A ∩ B) := interior_maximal h_subset h_open
    exact h_incl hx

theorem Topology.interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : interior A ⊆ interior (A ∪ B) := by
        have hAB : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact interior_mono hAB
      exact h_subset hxA
  | inr hxB =>
      have h_subset : interior B ⊆ interior (A ∪ B) := by
        have hAB : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact interior_mono hAB
      exact h_subset hxB

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx_closure : x ∈ closure A := by
      have : x ∈ A := interior_subset hx
      exact Set.subset_closure this
    exact ⟨hx_closure, hx⟩

theorem Topology.closure_inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no point belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_cl, hx_int⟩
  -- Every neighbourhood of `x` meets `A`, since `x ∈ closure A`.
  have h_nonempty : ((interior (Aᶜ)) ∩ A).Nonempty := by
    have h_closure := (mem_closure_iff).1 hx_cl
    exact h_closure _ isOpen_interior hx_int
  -- Pick a point in the non-empty intersection and derive a contradiction.
  rcases h_nonempty with ⟨y, ⟨hy_int_compl, hyA⟩⟩
  have hy_notA : y ∈ Aᶜ := interior_subset hy_int_compl
  exact (hy_notA hyA).elim

theorem Topology.closure_union_three_eq {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    closure (A ∪ B ∪ C) = closure A ∪ closure B ∪ closure C := by
  classical
  -- Apply the binary union lemma to `(A ∪ B)` and `C`.
  have h₁ : closure ((A ∪ B) ∪ C) =
      closure (A ∪ B) ∪ closure C :=
    Topology.closure_union_eq (A := A ∪ B) (B := C)
  -- Rewrite `closure (A ∪ B)` using the same lemma.
  have h₂ : closure (A ∪ B) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Assemble the pieces and tidy up associativity of `∪`.
  simpa [h₂, Set.union_assoc] using h₁

theorem Topology.P2_of_interiorClosure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) : Topology.P2 (A := A) := by
  -- From the hypothesis we immediately obtain that `A` is open.
  have hA_open : IsOpen A := by
    simpa [h] using (isOpen_interior : IsOpen (interior (closure A)))
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hA_open

theorem Topology.interior_closureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply subset_antisymm
  ·
    have h_sub : closure (interior A) ⊆ (A : Set X) :=
      Topology.closureInterior_subset_of_isClosed (A := A) hA_closed
    exact interior_mono h_sub
  ·
    have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_sub isOpen_interior

theorem Topology.closure_inter_subset_closure_left_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A ∩ B) ⊆ closure A ∩ B := by
  intro x hx
  -- First, use the general inclusion into the product of closures.
  have hx' : x ∈ closure A ∩ closure B :=
    (Topology.closure_inter_subset (A := A) (B := B)) hx
  -- Reduce membership in `closure B` to membership in `B` via closedness.
  have hxB : x ∈ B := by
    simpa [hB.closure_eq] using hx'.2
  exact ⟨hx'.1, hxB⟩

theorem Topology.isClosed_of_closureInterior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = A) : IsClosed A := by
  have : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using this

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    (⋃ i, interior (𝒜 i)) ⊆ interior (⋃ i, 𝒜 i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : interior (𝒜 i) ⊆ interior (⋃ j, 𝒜 j) := by
    have h_set_subset : (𝒜 i : Set X) ⊆ ⋃ j, 𝒜 j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_set_subset
  exact h_subset hx_i

theorem Topology.closure_union_interiorCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x ∈ closure A
    · exact Or.inl hx
    ·
      have hx_interior : x ∈ interior (Aᶜ) := by
        have h_eq := Topology.interior_compl_eq_compl_closure (A := A)
        have h_mem : x ∈ (closure A)ᶜ := hx
        simpa [h_eq] using h_mem
      exact Or.inr hx_interior

theorem closure_interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, compress the innermost five-step sequence using the existing lemma
  -- with `A := closure (interior A)`.
  have h₁ :=
    closure_interior_closure_interior_closure_interior_idempotent
      (A := closure (interior A))
  -- Next, compress the remaining three-step sequence.
  have h₂ := closure_interior_closure_idempotent (A := A)
  -- Combine the two equalities.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
          simpa using h₁
    _ = closure (interior A) := by
          simpa using h₂

theorem Topology.interiorClosure_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact Set.subset_closure hx

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) : IsClosed (closure A \ interior A) := by
  have h_closed_closure : IsClosed (closure A) := isClosed_closure
  have h_closed_compl : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  simpa [Set.diff_eq] using IsClosed.inter h_closed_closure h_closed_compl

theorem Topology.closureInteriorClosureInteriorClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_idempotent (A := closure A))

theorem Topology.closureInterior_inter_interiorCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We show that every point is *not* in the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_closure, hx_int_compl⟩
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  -- Since `x` lies in the closure of `interior A`, this neighbourhood
  -- meets `interior A`.
  have h_nonempty : ((interior (Aᶜ)) ∩ interior A).Nonempty := by
    have hx := (mem_closure_iff).1 hx_closure
    exact hx _ isOpen_interior hx_int_compl
  rcases h_nonempty with ⟨y, ⟨hy_int_compl, hy_intA⟩⟩
  -- Derive the contradiction `y ∈ A` and `y ∈ Aᶜ`.
  have hyA : y ∈ A := interior_subset hy_intA
  have hyA_compl : y ∈ Aᶜ := interior_subset hy_int_compl
  exact hyA_compl hyA

theorem Topology.isOpen_closure_iff_interiorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro h_open
    simpa using h_open.interior_eq
  · intro h_eq
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (closure A)))

theorem Topology.closure_inter_subset_closure_right_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) :
    closure (A ∩ B) ⊆ A ∩ closure B := by
  intro x hx
  -- First, use the general inclusion into the product of closures.
  have hx' : x ∈ closure A ∩ closure B :=
    (Topology.closure_inter_subset (A := A) (B := B)) hx
  -- Reduce membership in `closure A` to membership in `A` via closedness.
  have hxA : x ∈ A := by
    simpa [hA.closure_eq] using hx'.1
  exact ⟨hxA, hx'.2⟩

theorem Topology.closureInteriorCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_cl, hx_intA⟩
  -- Because `x` is in the closure of `interior (Aᶜ)` and
  -- `interior A` is an open neighbourhood of `x`,
  -- these two sets must meet.
  have h_nonempty : ((interior A) ∩ interior (Aᶜ)).Nonempty := by
    have h := (mem_closure_iff).1 hx_cl
    exact h _ isOpen_interior hx_intA
  -- But a point cannot lie in both `A` and `Aᶜ`.
  rcases h_nonempty with ⟨y, ⟨hy_intA, hy_intAc⟩⟩
  have hyA  : y ∈ A   := interior_subset hy_intA
  have hyAc : y ∈ Aᶜ := interior_subset hy_intAc
  exact hyAc hyA

theorem Topology.isClopen_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 (A := A)) :
    IsClosed A ∧ IsOpen A := by
  -- First, obtain `P3` from `P2`.
  have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 hP2
  -- Apply the result already proved for `P3`.
  exact Topology.isClopen_of_isClosed_of_P3 (A := A) hA_closed hP3

theorem Topology.closureInteriorClosure_isClosed {X : Type*} [TopologicalSpace X]
    (A : Set X) : IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    interior (⋂ i, 𝒜 i) ⊆ ⋂ i, interior (𝒜 i) := by
  intro x hx
  have h_forall : ∀ i, x ∈ interior (𝒜 i) := by
    intro i
    -- Since `⋂ j, 𝒜 j ⊆ 𝒜 i`, monotonicity of `interior` yields the result.
    have h_subset : (⋂ j, 𝒜 j : Set X) ⊆ 𝒜 i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_int_subset : interior (⋂ j, 𝒜 j) ⊆ interior (𝒜 i) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 h_forall

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := Set.subset_closure hxA
  simpa [h_open.interior_eq] using hx_closure

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) (hC : Topology.P3 (A := C)) :
    Topology.P3 (A := A ∪ B ∪ C) := by
  have hAB : Topology.P3 (A := A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hA hB
  simpa [Set.union_assoc] using
    (Topology.P3_union (A := A ∪ B) (B := C) hAB hC)

theorem Topology.closureInteriorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (A : Set X)) :
    closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
  -- Hence the interior of that closure is also `univ`.
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Taking the closure once more leaves the set unchanged.
  calc
    closure (interior (closure (A : Set X)))
        = closure (Set.univ : Set X) := by
          simpa [h_int]
    _ = (Set.univ : Set X) := by
          simpa [closure_univ]

theorem Topology.P3_iff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 (A := A) ↔ interior A = A := by
  -- First, express `P3` in terms of openness.
  have h₁ : Topology.P3 (A := A) ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed
  -- Openness is equivalent to equality with the interior.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hA_open
      simpa using hA_open.interior_eq
    · intro h_eq
      simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) :
    Topology.P2 (A := A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P2 (A := A ∪ B) :=
    Topology.P2_union (A := A) (B := B) hA hB
  -- Now union the result with `C`.
  simpa [Set.union_assoc] using
    (Topology.P2_union (A := A ∪ B) (B := C) hAB hC)

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 (A := A) ↔ interior A = A := by
  -- First, translate `P2` into openness using the existing equivalence.
  have h₁ : Topology.P2 (A := A) ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  -- Openness is equivalent to equality with the interior.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hA_open
      simpa using hA_open.interior_eq
    · intro h_eq
      simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem Topology.interior_closureDiffSelf_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X) \ A) = (∅ : Set X) := by
  classical
  -- We prove that `interior (closure A \ A)` contains no points.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hx
  -- `x` lies in the interior, hence in the set itself.
  have hx_diff : x ∈ closure A \ A :=
    (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hx
  -- In particular, `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx_diff.1
  -- Consider the open neighbourhood `U = interior (closure A \ A)` of `x`.
  have h_open : IsOpen (interior (closure A \ A)) := isOpen_interior
  have h_nonempty :
      ((interior (closure A \ A)) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure _ h_open hx
  -- Extract a point `y ∈ A` that is also in `interior (closure A \ A)`.
  rcases h_nonempty with ⟨y, hyU, hyA⟩
  -- But `interior (closure A \ A)` is contained in `closure A \ A`,
  -- so `y ∉ A`, contradicting `hyA`.
  have hy_notA : y ∉ A := by
    have : y ∈ closure A \ A :=
      (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hyU
    exact this.2
  exact hy_notA hyA

theorem Topology.closure_inter_interior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A ∩ interior A) = closure (interior A) := by
  -- Since `interior A ⊆ A`, the intersection simplifies.
  have h_inter : (A ∩ interior A : Set X) = interior A := by
    have : interior A ⊆ A := interior_subset
    exact Set.inter_eq_right.mpr this
  simpa [h_inter]

theorem Topology.closure_inter_closureCompl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∩ closure (Aᶜ) = closure A \ interior A := by
  -- First, rewrite `closure (Aᶜ)` using a previously proved lemma.
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  -- Reduce the goal to a set‐theoretic identity.
  calc
    closure A ∩ closure (Aᶜ) = closure A ∩ (interior A)ᶜ := by
      simpa [h]
    _ = closure A \ interior A := by
      -- Both sides are equal to `closure A ∩ (interior A)ᶜ`.
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, by
          -- `x ∈ (interior A)ᶜ` means `x ∉ interior A`.
          simpa using hx.2⟩
      · intro hx
        exact ⟨hx.1, by
          -- `x ∉ interior A` means `x ∈ (interior A)ᶜ`.
          simpa using hx.2⟩

theorem Topology.P1_inter_three_of_open {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A := A ∩ B ∩ C) := by
  -- The intersection of three open sets is open.
  have h_open : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    exact IsOpen.inter hAB hC
  -- Any open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A ∩ B ∩ C) h_open

theorem Topology.interior_union_eq_union_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B) = A ∪ B := by
  have h_open : IsOpen (A ∪ B) := IsOpen.union hA hB
  simpa using h_open.interior_eq

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) ↔ Topology.P3 (A := closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_isClosed (A := closure A) h_closed)

theorem Topology.interiorClosureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  intro x hx
  exact interior_subset hx

theorem Topology.P3_inter_three_of_open
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P3 (A := A ∩ B ∩ C) := by
  have h_open : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    exact IsOpen.inter hAB hC
  exact Topology.P3_of_isOpen (A := A ∩ B ∩ C) h_open

theorem Set.compl_compl {α : Type*} (s : Set α) : (sᶜ)ᶜ = s := by
  ext x
  simp

theorem Set.disjoint_compl_left {α : Type*} (s : Set α) : Disjoint s sᶜ := by
  exact (Set.disjoint_left).2 (by
    intro x hxS hxSc
    exact hxSc hxS)

theorem Topology.interior_inter_interiorCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no element belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_intA, hx_intAc⟩
  -- From membership in the interiors, deduce membership in the underlying sets.
  have hA  : x ∈ A   := interior_subset hx_intA
  have hAc : x ∈ Aᶜ := interior_subset hx_intAc
  -- The two memberships are incompatible.
  exact hAc hA

theorem Topology.boundary_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure (Aᶜ) := by
  classical
  intro x hx
  -- `x` lies in the closure of `A` but not in its interior.
  have hx_not_int : x ∉ interior (A : Set X) := hx.2
  -- We prove by contradiction that `x ∈ closure (Aᶜ)`.
  by_contra h_not
  -- The complement of `closure (Aᶜ)` is an open neighbourhood of `x`.
  set U : Set X := ((closure (Aᶜ) : Set X)ᶜ) with hU_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using (isClosed_closure : IsClosed (closure (Aᶜ))).isOpen_compl
  have hxU : x ∈ U := by
    have : x ∉ closure (Aᶜ) := by
      simpa using h_not
    simpa [hU_def] using this
  -- Show that `U ⊆ A`.  Indeed, if `y ∈ U` but `y ∉ A`, then `y ∈ Aᶜ`
  -- whence `y ∈ closure (Aᶜ)`, contradicting `y ∈ U = (closure (Aᶜ))ᶜ`.
  have hU_subset_A : U ⊆ (A : Set X) := by
    intro y hyU
    have hy_not_closure : y ∉ closure (Aᶜ) := by
      simpa [hU_def] using hyU
    by_cases hAy : y ∈ (A : Set X)
    · exact hAy
    · have hyAc : y ∈ (Aᶜ : Set X) := hAy
      have : y ∈ closure (Aᶜ) := subset_closure hyAc
      exact (hy_not_closure this).elim
  -- Hence `x` belongs to an open set `U` contained in `A`, so `x ∈ interior A`,
  -- contradicting `hx_not_int`.
  have hx_intA : x ∈ interior (A : Set X) := by
    -- `interior_maximal` supplies the required inclusion.
    have h_incl : U ⊆ interior (A : Set X) :=
      interior_maximal hU_subset_A hU_open
    exact h_incl hxU
  exact hx_not_int hx_intA

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B))
    (hC : Topology.P1 (A := C)) :
    Topology.P1 (A := A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (A := A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hA hB
  -- Now union the result with `C`.
  simpa [Set.union_assoc] using
    (Topology.P1_union (A := A ∪ B) (B := C) hAB hC)

theorem Topology.closureInterior_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior A = interior A := by
  simpa [interior_interior] using
    (Topology.closure_inter_interior_eq_interior (A := interior A))

theorem Topology.closureInterior_union_closureCompl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (A : Set X)) ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hxc : x ∈ closure (Aᶜ)
    · exact Or.inr hxc
    · -- Since `x ∉ closure (Aᶜ)`, the open set `U = (closure (Aᶜ))ᶜ`
      -- contains `x` and is contained in `A`.
      have hxU : x ∈ ((closure (Aᶜ) : Set X)ᶜ) := by
        simpa using hxc
      have hU_open : IsOpen ((closure (Aᶜ) : Set X)ᶜ) :=
        (isClosed_closure : IsClosed (closure (Aᶜ))).isOpen_compl
      have hU_subsetA : ((closure (Aᶜ) : Set X)ᶜ) ⊆ A := by
        intro y hy
        by_contra hAy
        have hyAc : y ∈ (Aᶜ : Set X) := hAy
        have : y ∈ closure (Aᶜ) := subset_closure hyAc
        exact hy this
      -- Hence `x ∈ interior A`.
      have hx_intA : x ∈ interior A := by
        have h_subset : ((closure (Aᶜ) : Set X)ᶜ) ⊆ interior A :=
          interior_maximal hU_subsetA hU_open
        exact h_subset hxU
      -- Therefore `x ∈ closure (interior A)`.
      have hx_closureInt : x ∈ closure (interior A) := subset_closure hx_intA
      exact Or.inl hx_closureInt

theorem Topology.interiorClosureCompl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_int_cl_compl, hx_intA⟩
  -- From `x ∈ interior (closure (Aᶜ))`, deduce `x ∈ closure (Aᶜ)`.
  have hx_cl_compl : x ∈ closure (Aᶜ) := interior_subset hx_int_cl_compl
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have h_subset : closure (Aᶜ : Set X) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  -- Hence `x ∉ interior A`, contradicting `hx_intA`.
  have hx_not_intA : x ∉ interior A := by
    have hx' : x ∈ (interior A)ᶜ := h_subset hx_cl_compl
    simpa using hx'
  exact hx_not_intA hx_intA

theorem Topology.boundary_subset_closure_inter_closureCompl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure A ∩ closure (Aᶜ) := by
  intro x hx
  -- `x` lies in `closure A`.
  have hx_closureA : x ∈ closure A := hx.1
  -- By a previously proven lemma, `x` also lies in `closure (Aᶜ)`.
  have hx_closureAc : x ∈ closure (Aᶜ) :=
    (Topology.boundary_subset_closure_compl (A := A)) hx
  -- Combine the two facts.
  exact ⟨hx_closureA, hx_closureAc⟩

theorem Topology.closure_inter_eq_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have h_closed : IsClosed (A ∩ B) := IsClosed.inter hA hB
  simpa using h_closed.closure_eq

theorem Topology.closure_subset_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ⊆ (Set.univ : Set X) := by
  intro x _
  trivial

theorem Topology.interior_closure_union_eq {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  have h := Topology.closure_union_eq (A) (B)
  simpa [h]

theorem Topology.interior_inter_closureCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ closure (Aᶜ) = (∅ : Set X) := by
  simpa [Set.inter_comm] using
    (Topology.closureCompl_inter_interior_eq_empty (A := A))

theorem Topology.P2_iff_isOpen_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    Topology.P2 (A := A) ↔ IsOpen A := by
  -- In a discrete topology every set is open.
  have hOpen : IsOpen A := isOpen_discrete _
  constructor
  · intro _; exact hOpen
  · intro _; exact Topology.P2_of_discrete (A := A)

theorem Topology.boundary_complement {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  classical
  calc
    closure (A : Set X) \ interior A
        = closure (A : Set X) ∩ closure (Aᶜ) := by
          simpa using
            (Topology.closure_inter_closureCompl_eq_closure_diff_interior
              (A := A)).symm
    _ = closure (Aᶜ) ∩ closure (A : Set X) := by
          simp [Set.inter_comm]
    _ = closure (Aᶜ) \ interior (Aᶜ) := by
          simpa using
            (Topology.closure_inter_closureCompl_eq_closure_diff_interior
              (A := Aᶜ))

theorem Topology.P2_inter_three_of_open
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P2 (A := A ∩ B ∩ C) := by
  -- The intersection of three open sets is open.
  have h_open : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    exact IsOpen.inter hAB hC
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A ∩ B ∩ C) h_open

theorem Topology.disjoint_interior_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior (A : Set X)) (closure A \ interior A) := by
  -- We use the characterization `Set.disjoint_left`.
  exact (Set.disjoint_left).2 (by
    intro x hx_int hx_boundary
    -- `hx_boundary.2` states that `x ∉ interior A`, contradicting `hx_int`.
    exact (hx_boundary.2) hx_int)

theorem Topology.interior_union_closureDiffInterior_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ (closure A \ interior A) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hx_int =>
        exact (Topology.interior_subset_closure (A := A)) hx_int
    | inr hx_diff =>
        exact hx_diff.1
  · intro hx_cl
    by_cases hx_int : x ∈ interior (A : Set X)
    · exact Or.inl hx_int
    · exact Or.inr ⟨hx_cl, hx_int⟩

theorem Topology.interior_iUnionClosure_subset_interiorClosure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X} :
    interior (⋃ i, closure (𝒜 i)) ⊆ interior (closure (⋃ i, 𝒜 i)) := by
  -- Use the previously proven inclusion between the unions themselves.
  have h_subset :
      (⋃ i, closure (𝒜 i) : Set X) ⊆ closure (⋃ i, 𝒜 i) :=
    Topology.iUnion_closure_subset_closure_iUnion (𝒜 := 𝒜)
  -- Monotonicity of `interior` yields the desired inclusion.
  exact interior_mono h_subset

theorem Topology.closureInterior_inter_interiorClosureInterior_eq_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior (closure (interior A)) =
      interior (closure (interior A)) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨interior_subset hx, hx⟩

theorem Topology.boundaryClosure_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int_cl⟩
  have hx_not_intA : x ∉ interior (A : Set X) := by
    intro hx_intA
    have h_subset : interior (A : Set X) ⊆ interior (closure A) :=
      Topology.interior_subset_interiorClosure (A := A)
    have : x ∈ interior (closure A) := h_subset hx_intA
    exact hx_not_int_cl this
  exact ⟨hx_cl, hx_not_intA⟩

theorem Topology.union_interiors_eq_compl_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ interior (Aᶜ) = (closure A \ interior A)ᶜ := by
  classical
  -- Express `interior (Aᶜ)` in terms of `closure A`.
  have hIntComp : interior (Aᶜ : Set X) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Rewrite the complement of the boundary and simplify.
  simpa [hIntComp, Set.diff_eq, Set.compl_inter, Set.compl_compl,
        Set.union_comm, Set.union_left_comm, Set.union_assoc]

theorem Topology.boundary_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    closure (A : Set X) \ interior A = A \ interior A := by
  simpa [hA.closure_eq]

theorem Topology.boundary_eq_closure_diff_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (A : Set X) \ interior A = closure A \ A := by
  simpa [hA.interior_eq]

theorem Topology.boundary_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A : Set X) \ interior A ⊆ A := by
  intro x hx
  -- `x` lies in the closure of `A`, but `A` is closed, hence
  -- `closure A = A`.  This places `x` inside `A`.
  simpa [hA.closure_eq] using hx.1

theorem Topology.P1_iff_isOpen_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ IsOpen A := by
  constructor
  · intro _; exact isOpen_discrete _
  · intro hA_open; exact Topology.P1_of_isOpen (A := A) hA_open

theorem Topology.closure_iInter_eq_iInter_of_isClosed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, IsClosed (𝒜 i)) :
    closure (⋂ i, 𝒜 i) = ⋂ i, 𝒜 i := by
  have hClosed : IsClosed (⋂ i, 𝒜 i) := isClosed_iInter h𝒜
  simpa [hClosed.closure_eq]

theorem Topology.closureInterior_eq_univ_of_open_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (A : Set X)) (h_dense : Dense (A : Set X)) :
    closure (interior A) = (Set.univ : Set X) := by
  have h_int : interior A = A := h_open.interior_eq
  have h_cl : closure A = (Set.univ : Set X) := h_dense.closure_eq
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = (Set.univ : Set X) := by
      simpa [h_cl]

theorem Topology.boundaryInterior_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  have hx_closureInt : x ∈ closure (interior A) := hx.1
  have hx_not_int : x ∉ interior A := hx.2
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hx_closureA : x ∈ closure A := h_subset hx_closureInt
  exact ⟨hx_closureA, hx_not_int⟩

theorem closure_eq_closureInterior_union_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = closure (interior A) ∪ (closure A \ interior A) := by
  ext x
  constructor
  · intro hx_clA
    by_cases hx_intA : x ∈ interior (A : Set X)
    · -- `x` is in the interior, hence in `closure (interior A)`.
      have : x ∈ closure (interior A) := by
        exact subset_closure hx_intA
      exact Or.inl this
    · -- `x` is not in the interior, so it belongs to the boundary part.
      exact Or.inr ⟨hx_clA, hx_intA⟩
  · intro hx_union
    cases hx_union with
    | inl hx_cl_int =>
        -- `closure (interior A)` is contained in `closure A`.
        have h_subset := Topology.closureInterior_subset_closure (A := A)
        exact h_subset hx_cl_int
    | inr hx_boundary =>
        exact hx_boundary.1

theorem Topology.boundary_subset_compl_iff_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior A ⊆ Aᶜ ↔ IsOpen A := by
  classical
  constructor
  · intro h_boundary
    -- We show `A` equals its interior.
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        by_cases hx_int : x ∈ interior A
        · exact hx_int
        ·
          -- Otherwise `x` lies in the boundary, contradicting `h_boundary`.
          have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
          have hx_bd : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, hx_int⟩
          have hx_compl : x ∈ (Aᶜ : Set X) := h_boundary hx_bd
          exact (hx_compl hxA).elim
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    intro x hx_bd
    -- Using `interior A = A` for open sets.
    have h_int_eq : interior A = A := hA_open.interior_eq
    have hx_not_int : x ∉ interior A := hx_bd.2
    have hx_not_A : x ∉ A := by
      simpa [h_int_eq] using hx_not_int
    simpa using hx_not_A

theorem Topology.boundary_union_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ B) \ interior (A ∪ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hx_cl_union, hx_not_int_union⟩
  -- From `x ∈ closure (A ∪ B)` deduce `x ∈ closure A ∪ closure B`.
  have hx_closure_union : x ∈ closure A ∪ closure B := by
    have h_eq := (Topology.closure_union_eq (A) (B))
    have : x ∈ closure (A ∪ B) := hx_cl_union
    simpa [h_eq] using this
  -- `x` is not in `interior A` (otherwise it would be in `interior (A ∪ B)`).
  have h_not_intA : x ∉ interior A := by
    intro hx_intA
    have h_subset : interior A ⊆ interior (A ∪ B) := by
      have h_sub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono h_sub
    exact hx_not_int_union (h_subset hx_intA)
  -- Likewise, `x` is not in `interior B`.
  have h_not_intB : x ∉ interior B := by
    intro hx_intB
    have h_subset : interior B ⊆ interior (A ∪ B) := by
      have h_sub : (B : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      exact interior_mono h_sub
    exact hx_not_int_union (h_subset hx_intB)
  -- Finish by cases on membership in `closure A ∪ closure B`.
  cases hx_closure_union with
  | inl hx_clA =>
      exact Or.inl ⟨hx_clA, h_not_intA⟩
  | inr hx_clB =>
      exact Or.inr ⟨hx_clB, h_not_intB⟩

theorem Topology.boundary_subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    closure (A : Set X) \ interior A ⊆ closure (interior A) := by
  intro x hx
  -- `hx` provides `x ∈ closure A`.
  have hx_closureA : x ∈ closure A := hx.1
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have h_closure_subset : closure A ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := hP1
    have h_closure : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hA_subset
    simpa [closure_closure] using h_closure
  -- Therefore, `x ∈ closure (interior A)`.
  exact h_closure_subset hx_closureA

theorem Topology.boundary_inter_subset_union_boundary
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) \ interior (A ∩ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  classical
  intro x hx
  rcases hx with ⟨hx_clAB, hx_not_intAB⟩
  -- `x` lies in the closures of both `A` and `B`.
  have h_cl_subset := (Topology.closure_inter_subset (A := A) (B := B)) hx_clAB
  have hx_clA : x ∈ closure A := h_cl_subset.1
  have hx_clB : x ∈ closure B := h_cl_subset.2
  -- Express `interior (A ∩ B)` via interiors of the factors.
  have h_int_eq : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  -- At least one of `x ∉ interior A`, `x ∉ interior B` must hold.
  by_cases hx_intA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x ∈ interior (A ∩ B)`.
    have hx_not_intB : x ∉ interior B := by
      intro hx_intB
      have : x ∈ interior (A ∩ B) := by
        -- Rewriting via `h_int_eq`.
        have : x ∈ interior A ∩ interior B := ⟨hx_intA, hx_intB⟩
        simpa [h_int_eq] using this
      exact hx_not_intAB this
    -- Hence `x` is in the boundary of `B`.
    exact Or.inr ⟨hx_clB, hx_not_intB⟩
  · -- `x` is not in `interior A`, so it lies in the boundary of `A`.
    exact Or.inl ⟨hx_clA, hx_intA⟩

theorem Topology.interior_closure_union_three_eq {X : Type*} [TopologicalSpace X]
    (A B C : Set X) :
    interior (closure (A ∪ B ∪ C : Set X)) =
      interior (closure A ∪ closure B ∪ closure C) := by
  -- Reassociate the union to fit the binary lemmas.
  have h₁ : (A ∪ B ∪ C : Set X) = (A ∪ B) ∪ C := by
    simpa [Set.union_assoc]
  -- Use the two–set lemma for closures.
  have h₂ : (closure (A ∪ B) : Set X) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Apply the binary lemma twice, rewriting along the way.
  calc
    interior (closure (A ∪ B ∪ C : Set X))
        = interior (closure ((A ∪ B) ∪ C)) := by
          simpa [h₁]
    _ = interior (closure (A ∪ B) ∪ closure C) := by
          simpa using
            (Topology.interior_closure_union_eq (A := A ∪ B) (B := C))
    _ = interior ((closure A ∪ closure B) ∪ closure C) := by
          simpa [h₂]
    _ = interior (closure A ∪ closure B ∪ closure C) := by
          simpa [Set.union_assoc]

theorem Topology.closureInterior_inter_closed_eq_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ∩ A = closure (interior A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have hxA : x ∈ A :=
      (Topology.closureInterior_subset_of_isClosed (A := A) hA) hx
    exact ⟨hx, hxA⟩

theorem Topology.boundary_empty {X : Type*} [TopologicalSpace X] :
    closure ((∅ : Set X)) \ interior (∅ : Set X) = (∅ : Set X) := by
  simp

theorem Topology.inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no element belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxA, hxIntCompl⟩
  have hxAc : x ∈ (Aᶜ : Set X) := interior_subset hxIntCompl
  exact hxAc hxA

theorem Topology.boundary_eq_empty_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_interior : interior (A : Set X) = A := hA_open.interior_eq
  simpa [h_closure, h_interior, Set.diff_self]

theorem Topology.P1_iff_boundary_subset_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (A := A) ↔ (A \ interior A) ⊆ closure (interior A) := by
  classical
  -- First, show that `P1` implies the boundary inclusion.
  constructor
  · intro hP1
    -- We can reuse the general lemma and simplify using `hA_closed`.
    have h :=
      Topology.boundary_subset_closureInterior_of_P1 (A := A) hP1
    simpa [hA_closed.closure_eq] using h
  · intro hBoundary
    -- To prove `P1`, pick any `x ∈ A`.
    dsimp [Topology.P1] at *
    intro x hxA
    by_cases hxInt : x ∈ interior A
    · -- Points of `interior A` are certainly in `closure (interior A)`.
      exact subset_closure hxInt
    · -- Otherwise `x` lies in the boundary, which is contained in the closure.
      have hx_boundary : x ∈ A \ interior A := ⟨hxA, hxInt⟩
      exact hBoundary hx_boundary

theorem Topology.isClopen_of_boundary_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) \ interior A = (∅ : Set X)) :
    IsClosed A ∧ IsOpen A := by
  classical
  -- Step 1: `closure A ⊆ interior A`.
  have h_subset : (closure (A : Set X)) ⊆ interior A := by
    intro x hx_cl
    by_contra hx_int
    have : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, hx_int⟩
    have : x ∈ (∅ : Set X) := by
      simpa [h] using this
    exact this.elim
  -- Step 2: `closure A = interior A`.
  have h_eq_cl_int :
      (closure (A : Set X)) = interior A :=
    Set.Subset.antisymm h_subset
      (Topology.interior_subset_closure (A := A))
  -- Step 3: `closure A = A`.
  have h_cl_eq : (closure (A : Set X)) = A := by
    apply Set.Subset.antisymm
    · intro x hx_cl
      -- `x ∈ closure A = interior A ⊆ A`.
      have : x ∈ interior A := by
        simpa [h_eq_cl_int] using hx_cl
      exact interior_subset this
    · exact subset_closure
  -- Step 4: `interior A = A`.
  have h_int_eq : interior A = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
      have : x ∈ interior A := h_subset hx_cl
      exact this
  -- Step 5: conclude `A` is clopen.
  have h_closed : IsClosed A := by
    have : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_cl_eq] using this
  have h_open : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [h_int_eq] using this
  exact ⟨h_closed, h_open⟩

theorem Topology.closureCompl_union_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (Aᶜ) ∪ A = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x ∈ A
    · exact Or.inr hx
    ·
      have hx_compl : x ∈ (Aᶜ : Set X) := hx
      have hx_closure : x ∈ closure (Aᶜ : Set X) := subset_closure hx_compl
      exact Or.inl hx_closure

theorem Topology.interior_closure_interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h₁ :=
    (interior_closure_idempotent (A := interior (closure A)))
  have h₂ :=
    (interior_closure_idempotent (A := A))
  simpa using (Eq.trans h₁ h₂)

theorem Topology.interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First, compress the innermost five-step pattern.
  have h₁ :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) :=
    interior_closure_interior_idempotent (A := A)
  -- Substitute the reduction and apply the two-step idempotency lemma.
  simpa [h₁] using
    (interior_closure_idempotent (A := interior A))

theorem Topology.boundary_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.boundary_eq_empty_iff_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X) \ interior A = (∅ : Set X)) ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro h
    exact Topology.isClopen_of_boundary_eq_empty (A := A) h
  · rintro ⟨hClosed, hOpen⟩
    exact Topology.boundary_eq_empty_of_isClopen (A := A) hClosed hOpen

theorem Topology.closureInteriorClosure_eq_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    closure (interior (closure A)) = closure (interior A) := by
  simpa [hA_closed.closure_eq]

theorem Topology.closureFrontier_eq_self
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = frontier A := by
  have h_closed : IsClosed (frontier A) := isClosed_frontier
  simpa using h_closed.closure_eq

theorem Topology.interior_intersection_closures_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono h_subset) hx
  exact ⟨hxA, hxB⟩

theorem Topology.frontier_eq_closure_diff_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) = closure A \ A := by
  simpa [frontier, hA.interior_eq]

theorem Topology.frontier_eq_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier (A : Set X) = A \ interior A := by
  simpa [frontier, hA.closure_eq]

theorem Topology.boundary_eq_empty_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] (A : Set X) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  have hClosed : IsClosed (A : Set X) := isClosed_discrete _
  have hOpen   : IsOpen   (A : Set X) := isOpen_discrete _
  simpa using Topology.boundary_eq_empty_of_isClopen (A := A) hClosed hOpen

theorem Topology.frontier_univ {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  classical
  simp [frontier, closure_univ, interior_univ]

theorem Topology.boundary_union_three_subset_union_boundary
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A ∪ B ∪ C) \ interior (A ∪ B ∪ C) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) ∪
        (closure C \ interior C) := by
  intro x hx
  -- First, treat the union as `((A ∪ B) ∪ C)` and apply the two‐set lemma.
  have h₁ :
      x ∈ (closure (A ∪ B) \ interior (A ∪ B)) ∪
          (closure C \ interior C) :=
    (Topology.boundary_union_subset_union_boundary
        (A := A ∪ B) (B := C)) hx
  cases h₁ with
  | inl hAB =>
      -- Now decompose the boundary of `A ∪ B`.
      have h₂ :
          x ∈ (closure A \ interior A) ∪ (closure B \ interior B) :=
        (Topology.boundary_union_subset_union_boundary
            (A := A) (B := B)) hAB
      cases h₂ with
      | inl hA =>
          exact Or.inl (Or.inl hA)
      | inr hB =>
          exact Or.inl (Or.inr hB)
  | inr hC =>
      exact Or.inr hC

theorem Topology.closure_diff_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_cl_int⟩
  have hx_not_int : x ∉ interior A := by
    intro hx_int
    have : x ∈ closure (interior A) := subset_closure hx_int
    exact hx_not_cl_int this
  exact ⟨hx_cl, hx_not_int⟩

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.P3_iff_isOpen_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P3 (A := A) ↔ IsOpen A := by
  constructor
  · intro _; simpa using (isOpen_discrete _)
  · intro _; exact Topology.P3_of_discrete (A := A)

theorem Topology.interior_union_interior_eq_self {X : Type*} [TopologicalSpace X]
    (A : Set X) : interior (A ∪ interior A) = interior A := by
  -- First, observe that `A ∪ interior A` is just `A`,
  -- since `interior A ⊆ A`.
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hA      => exact hA
      | inr hIntA   => exact interior_subset hIntA
    · intro hx
      exact Or.inl hx
  -- Rewrite using this equality.
  simpa [h_union]

theorem Topology.closure_union_four_eq {X : Type*} [TopologicalSpace X]
    (A B C D : Set X) :
    closure (A ∪ B ∪ C ∪ D) =
      closure A ∪ closure B ∪ closure C ∪ closure D := by
  classical
  -- Regroup to apply the binary union lemma.
  have h₁ : (A ∪ B ∪ C ∪ D : Set X) = ((A ∪ B ∪ C) ∪ D) := by
    simpa [Set.union_assoc]
  -- Use the three–set lemma for the inner union.
  have h₂ :
      closure (A ∪ B ∪ C) = closure A ∪ closure B ∪ closure C :=
    Topology.closure_union_three_eq (A := A) (B := B) (C := C)
  calc
    closure (A ∪ B ∪ C ∪ D)
        = closure ((A ∪ B ∪ C) ∪ D) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C) ∪ closure D := by
          simpa using
            (Topology.closure_union_eq (A := A ∪ B ∪ C) (B := D))
    _ = (closure A ∪ closure B ∪ closure C) ∪ closure D := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D := by
          simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm]

theorem Topology.interiorClosure_diff_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_int_cl, hx_not_cl_int⟩
  -- `x` lies in `closure A` because `interior (closure A) ⊆ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := interior_subset hx_int_cl
  -- Show that `x` is not in `interior A`.
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    have : x ∈ closure (interior A) := subset_closure hx_intA
    exact hx_not_cl_int this
  exact ⟨hx_clA, hx_not_intA⟩

theorem Set.compl_compl_safe {α : Type*} (s : Set α) :
    ((sᶜ)ᶜ : Set α) = s := by
  ext x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

theorem Topology.frontier_union_subset_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Decompose the hypothesis `hx` into its two components.
  have hx_cl_union : x ∈ closure (A ∪ B) := hx.1
  have hx_not_int_union : x ∉ interior (A ∪ B) := hx.2
  -- Because `A` and `B` are open, their union is open, hence its interior
  -- is just itself.
  have h_int_union : interior (A ∪ B) = A ∪ B := by
    have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
    simpa using h_open_union.interior_eq
  -- Translate the non‐interiority condition.
  have hx_not_union : x ∉ A ∪ B := by
    simpa [h_int_union] using hx_not_int_union
  -- Rewrite membership in the closure of the union.
  have hx_closure_split : x ∈ closure A ∪ closure B := by
    have h_eq := Topology.closure_union_eq (A := A) (B := B)
    simpa [h_eq] using hx_cl_union
  -- Break into cases.
  cases hx_closure_split with
  | inl hx_clA =>
      -- `x` lies in the closure of `A` but not in its interior,
      -- so `x` is in the frontier of `A`.
      have hx_not_intA : x ∉ interior A := by
        intro hx_intA
        have hxA : x ∈ A := interior_subset hx_intA
        exact hx_not_union (Or.inl hxA)
      exact Or.inl ⟨hx_clA, hx_not_intA⟩
  | inr hx_clB =>
      -- Symmetric argument for `B`.
      have hx_not_intB : x ∉ interior B := by
        intro hx_intB
        have hxB : x ∈ B := interior_subset hx_intB
        exact hx_not_union (Or.inr hxB)
      exact Or.inr ⟨hx_clB, hx_not_intB⟩

theorem frontier_eq_empty_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    frontier (A : Set X) = (∅ : Set X) := by
  classical
  -- In a discrete space, every set is both closed and open.
  have h_closure : closure (A : Set X) = A := (isClosed_discrete _).closure_eq
  have h_interior : interior (A : Set X) = A := (isOpen_discrete _).interior_eq
  -- Hence the frontier, defined as `closure A \ interior A`, is empty.
  simp [frontier, h_closure, h_interior, Set.diff_self]

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : frontier (A : Set X) ⊆ A := by
  intro x hx
  -- `hx` provides `x ∈ closure A`.
  have hx_cl : x ∈ closure (A : Set X) := hx.1
  -- Since `A` is closed, we have `closure A = A`.
  have h_cl_eq : closure (A : Set X) = A := hA.closure_eq
  -- The desired result follows by rewriting.
  simpa [h_cl_eq] using hx_cl

theorem Topology.P1_iff_isClosed_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ IsClosed A := by
  constructor
  · intro _; simpa using (isClosed_discrete _)
  · intro _; exact Topology.P1_of_discrete (A := A)

theorem Topology.P3_iff_isClosed_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P3 (A := A) ↔ IsClosed A := by
  constructor
  · intro _; simpa using (isClosed_discrete _)
  · intro _; exact Topology.P3_of_discrete (A := A)

theorem Topology.frontier_interior_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) = closure (interior A) \ interior A := by
  simp [frontier, interior_interior]

theorem Topology.closure_union_five_eq {X : Type*} [TopologicalSpace X]
    (A B C D E : Set X) :
    closure (A ∪ B ∪ C ∪ D ∪ E) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
  classical
  -- Reassociate the union to apply the binary union lemma.
  have h₁ : (A ∪ B ∪ C ∪ D ∪ E : Set X) = ((A ∪ B ∪ C ∪ D) ∪ E) := by
    simpa [Set.union_assoc]
  -- Use the four–set lemma for the inner union.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D) =
        closure A ∪ closure B ∪ closure C ∪ closure D :=
    Topology.closure_union_four_eq (A := A) (B := B) (C := C) (D := D)
  -- Assemble the pieces.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E)
        = closure ((A ∪ B ∪ C ∪ D) ∪ E) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C ∪ D) ∪ closure E := by
          simpa using
            (Topology.closure_union_eq (A := A ∪ B ∪ C ∪ D) (B := E))
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D) ∪ closure E := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E := by
          simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]

theorem Topology.closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- Since `interior B ⊆ B`, the intersection with `A` is contained accordingly.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem Topology.open_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal subset_closure hA

theorem Topology.interior_iUnion_eq_iUnion_of_open
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {𝒜 : ι → Set X}
    (h𝒜 : ∀ i, IsOpen (𝒜 i)) :
    interior (⋃ i, 𝒜 i) = ⋃ i, 𝒜 i := by
  have h_open : IsOpen (⋃ i, 𝒜 i) := isOpen_iUnion (fun i ↦ h𝒜 i)
  simpa using h_open.interior_eq

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure B ⊆ closure (A \ B) := by
  classical
  intro x hx
  rcases hx with ⟨hx_clA, hx_not_clB⟩
  -- Obtain an open neighbourhood `u` of `x` disjoint from `B`.
  have h_exists : ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ u ∩ B = ∅ := by
    by_contra h
    push_neg at h
    have : x ∈ closure B := (mem_closure_iff).2 h
    exact hx_not_clB this
  rcases h_exists with ⟨u, hu_open, hxu, hu_disj⟩
  -- Show that every open neighbourhood of `x` meets `A \\ B`.
  have key : ∀ s : Set X, IsOpen s → x ∈ s → (s ∩ (A \ B)).Nonempty := by
    intro s hs hxs
    -- Work inside `s ∩ u`, an open neighbourhood of `x`.
    have hsu_open : IsOpen (s ∩ u) := IsOpen.inter hs hu_open
    have hx_su : x ∈ s ∩ u := ⟨hxs, hxu⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have h_nonempty : ((s ∩ u) ∩ A).Nonempty := by
      have h_closure := (mem_closure_iff).1 hx_clA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
        h_closure (s ∩ u) hsu_open hx_su
    rcases h_nonempty with ⟨y, ⟨⟨hy_s, hy_u⟩, hyA⟩⟩
    -- `u` is disjoint from `B`, hence `y ∉ B`.
    have hy_notB : y ∉ B := by
      intro hyB
      have : y ∈ u ∩ B := ⟨hy_u, hyB⟩
      have : y ∈ (∅ : Set X) := by
        simpa [hu_disj] using this
      exact this.elim
    -- Produce the required point in `s ∩ (A \\ B)`.
    exact ⟨y, ⟨hy_s, ⟨hyA, hy_notB⟩⟩⟩
  -- Conclude that `x ∈ closure (A \\ B)`.
  exact (mem_closure_iff).2 key

theorem Topology.frontier_inter_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Decompose `hx` into closure and non‐interior parts.
  have hx_cl : x ∈ closure (A ∩ B : Set X) := hx.1
  have hx_not_int : x ∉ interior (A ∩ B : Set X) := hx.2
  -- `closure (A ∩ B)` is contained in `closure A ∩ closure B`.
  have h_cl_subset :
      closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  have hx_clA : x ∈ closure A := (h_cl_subset hx_cl).1
  have hx_clB : x ∈ closure B := (h_cl_subset hx_cl).2
  -- Rewrite `interior (A ∩ B)` using interiors of the factors.
  have h_int_eq :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  have hx_not_intAB : x ∉ interior A ∩ interior B := by
    have : x ∉ interior (A ∩ B : Set X) := hx_not_int
    simpa [h_int_eq] using this
  by_cases hx_intA : x ∈ interior A
  · -- Then `x ∉ interior B`, so `x ∈ frontier B`.
    have hx_not_intB : x ∉ interior B := by
      intro hx_intB
      have : x ∈ interior A ∩ interior B := ⟨hx_intA, hx_intB⟩
      exact hx_not_intAB this
    have hx_frontierB : x ∈ frontier B := ⟨hx_clB, hx_not_intB⟩
    exact Or.inr hx_frontierB
  · -- Otherwise `x ∈ frontier A`.
    have hx_frontierA : x ∈ frontier A := ⟨hx_clA, hx_intA⟩
    exact Or.inl hx_frontierA

theorem frontier_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (Aᶜ : Set X) = frontier (A : Set X) := by
  classical
  -- Express the closure and interior of a complement via complements.
  have h_cl : closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  have h_int : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Substitute the formulas and simplify.
  simp [frontier, h_cl, h_int, Set.diff_eq, Set.compl_compl,
        Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]

theorem Topology.interior_inter_closure_eq_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∩ closure A) = interior A := by
  -- We prove the two inclusions separately.
  apply subset_antisymm
  · -- `interior (A ∩ closure A)` is contained in `interior A`
    have h_subset : (A ∩ closure A : Set X) ⊆ A := by
      intro x hx; exact hx.1
    exact interior_mono h_subset
  · -- `interior A` is open and contained in `A ∩ closure A`,
    -- hence it is contained in the interior of that set.
    have h_subset : (interior A : Set X) ⊆ A ∩ closure A := by
      intro x hx
      have hxA : x ∈ A := interior_subset hx
      have hx_cl : x ∈ closure A := subset_closure hxA
      exact ⟨hxA, hx_cl⟩
    have h_open : IsOpen (interior A) := isOpen_interior
    exact interior_maximal h_subset h_open

theorem Topology.frontier_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure (A : Set X)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_cl_cl, hx_not_int_cl⟩
  -- `x` lies in the closure of `A`.
  have hx_cl : x ∈ closure (A : Set X) := by
    simpa [closure_closure] using hx_cl_cl
  -- Show that `x` is not in the interior of `A`.
  have hx_not_int : x ∉ interior (A : Set X) := by
    intro hx_int
    have : x ∈ interior (closure (A : Set X)) :=
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
    exact hx_not_int_cl this
  exact ⟨hx_cl, hx_not_int⟩

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- `hx` gives membership in the closure of `A ∪ B`
  -- and non-membership in its interior.
  have hx_cl_union : x ∈ closure (A ∪ B : Set X) := hx.1
  have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := hx.2
  -- From `hx_not_int_union`, deduce non-membership in the interiors of `A` and `B`.
  have h_not_intA : x ∉ interior A := by
    intro hx_intA
    have h_subset : interior A ⊆ interior (A ∪ B) :=
      interior_mono (by
        intro y hy
        exact Or.inl hy)
    exact hx_not_int_union (h_subset hx_intA)
  have h_not_intB : x ∉ interior B := by
    intro hx_intB
    have h_subset : interior B ⊆ interior (A ∪ B) :=
      interior_mono (by
        intro y hy
        exact Or.inr hy)
    exact hx_not_int_union (h_subset hx_intB)
  -- Rewrite `closure (A ∪ B)` as the union of the closures.
  have h_eq : closure (A ∪ B : Set X) = closure A ∪ closure B :=
    (Topology.closure_union_eq (A := A) (B := B))
  have hx_cl_AB : x ∈ closure A ∪ closure B := by
    simpa [h_eq] using hx_cl_union
  -- Conclude that `x` lies in at least one of the desired frontiers.
  cases hx_cl_AB with
  | inl hx_clA =>
      exact Or.inl ⟨hx_clA, h_not_intA⟩
  | inr hx_clB =>
      exact Or.inr ⟨hx_clB, h_not_intB⟩



theorem Topology.closure_inter_interior_subset_inter_closures
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  -- `interior B` is contained in `B`.
  have h₁ : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  have h₂ : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h₁
  -- Use the existing lemma for the intersection.
  have h₃ : closure (A ∩ B) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  -- Chain the inclusions.
  exact subset_trans h₂ h₃

theorem Topology.frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = closure A \ interior A := by
  rfl

theorem Topology.frontier_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior (A : Set X)) ⊆ frontier A := by
  intro x hx
  -- Decompose membership in the frontier of `interior A`.
  rcases hx with ⟨hx_cl_int, hx_not_int_int⟩
  -- `closure (interior A)` is contained in `closure A`.
  have hx_clA : x ∈ closure (A : Set X) :=
    (closure_mono (interior_subset : interior A ⊆ A)) hx_cl_int
  -- `interior (interior A)` coincides with `interior A`.
  have hx_not_intA : x ∉ interior (A : Set X) := by
    simpa [interior_interior] using hx_not_int_int
  exact ⟨hx_clA, hx_not_intA⟩

theorem Topology.frontier_subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    frontier (A : Set X) ⊆ closure (interior A) := by
  intro x hx
  -- `hx` gives `x ∈ closure A`.
  have hx_closureA : x ∈ closure (A : Set X) := hx.1
  -- From `P1`, obtain `closure A ⊆ closure (interior A)`.
  have h_subset : closure (A : Set X) ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using closure_mono hA
  -- Conclude the desired membership.
  exact h_subset hx_closureA

theorem Topology.interior_eq_closure_iff_isClopen {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = closure A ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro hEq
    -- First, deduce `A = interior A`.
    have hA_sub_int : (A : Set X) ⊆ interior A := by
      have hA_sub_cl : (A : Set X) ⊆ closure A := subset_closure
      simpa [hEq] using hA_sub_cl
    have h_int_eq : interior A = (A : Set X) :=
      subset_antisymm interior_subset hA_sub_int
    -- Next, deduce `A = closure A`.
    have h_cl_eq : closure A = (A : Set X) := by
      calc
        closure A = interior A := by
          symm; simpa using hEq
        _ = A := by
          simpa using h_int_eq
    -- Conclude that `A` is both closed and open.
    have hOpen : IsOpen (A : Set X) := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have hClosed : IsClosed (A : Set X) := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact ⟨hClosed, hOpen⟩
  · rintro ⟨hClosed, hOpen⟩
    -- From clopeness, both interior and closure equal `A`.
    have h_int : interior (A : Set X) = A := hOpen.interior_eq
    have h_cl  : closure (A : Set X) = A := hClosed.closure_eq
    simpa [h_int, h_cl]

theorem Topology.frontier_eq_inter_closure_closureCompl
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = closure A ∩ closure (Aᶜ) := by
  have h₁ := Topology.frontier_eq_closure_diff_interior (A := A)
  have h₂ := (Topology.closure_inter_closureCompl_eq_closure_diff_interior (A := A)).symm
  simpa using h₁.trans h₂

theorem Topology.frontier_eq_empty_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    frontier (A : Set X) = (∅ : Set X) := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_interior : interior (A : Set X) = A := hA_open.interior_eq
  simp [frontier, h_closure, h_interior, Set.diff_self]

theorem Topology.frontier_eq_compl_of_open_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_dense : Dense (A : Set X)) :
    frontier (A : Set X) = (Aᶜ : Set X) := by
  have h_frontier :
      frontier (A : Set X) = closure (A : Set X) \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA_open
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hA_dense.closure_eq
  simpa [h_closure, Set.diff_eq, Set.inter_univ, Set.univ_inter] using h_frontier

theorem Topology.frontier_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `hx` gives that `x` is in the closure of `A ∩ B`.
  have h_cl : x ∈ closure (A ∩ B : Set X) := hx.1
  -- The closure of an intersection is contained in the intersection
  -- of the closures.
  have h_subset : closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  -- Combining the two facts yields the desired membership.
  exact h_subset h_cl

theorem Topology.frontier_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- `hx.1` gives `x ∈ closure (interior A)`.
  have hx_closureInt : x ∈ closure (interior A) := hx.1
  -- Since `interior A ⊆ A`, taking closures yields the desired inclusion.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact h_subset hx_closureInt

theorem Topology.frontier_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simp [frontier]



theorem Topology.frontier_subset_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (Aᶜ) := by
  intro x hx
  -- Re-express `frontier A` as `closure A ∩ closure Aᶜ`.
  have h_inter : x ∈ closure (A : Set X) ∩ closure (Aᶜ) := by
    have h_eq := Topology.frontier_eq_inter_closure_closureCompl (A := A)
    simpa [h_eq] using hx
  -- Extract the membership in `closure Aᶜ`.
  exact h_inter.2



theorem Topology.interior_diff_subset_left {X : Type*} [TopologicalSpace X]
    (A B : Set X) : interior (A \ B : Set X) ⊆ interior A := by
  intro x hx
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the claim.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  exact (interior_mono h_subset) hx

theorem Topology.closure_subset_iff_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A : Set X) ⊆ B ↔ A ⊆ B := by
  constructor
  · intro hSub x hxA
    have : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub this
  · intro hSub
    have : closure (A : Set X) ⊆ closure B := closure_mono hSub
    simpa [hB.closure_eq] using this

theorem Topology.closure_subset_iff_subset_of_isClosed' {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A : Set X) ⊆ B ↔ A ⊆ B := by
  constructor
  · intro hSub x hxA
    exact hSub (subset_closure hxA)
  · intro hSub
    have h : closure (A : Set X) ⊆ closure B := closure_mono hSub
    simpa [hB.closure_eq] using h

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    frontier (A : Set X) ⊆ closure B := by
  intro x hx
  -- From `hx` we obtain `x ∈ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := hx.1
  -- Monotonicity of `closure` gives `closure A ⊆ closure B`.
  have h_closure_mono : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Hence `x ∈ closure B`.
  exact h_closure_mono hx_clA

theorem Topology.frontier_union_eq_union_frontier_of_open_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hAB : Disjoint (A : Set X) B) :
    frontier (A ∪ B : Set X) = frontier A ∪ frontier B := by
  classical
  -- One inclusion is already available.
  have h₁ :
      frontier (A ∪ B : Set X) ⊆ frontier A ∪ frontier B :=
    frontier_union_subset_of_open (A := A) (B := B) hA hB
  -- For the reverse inclusion, treat each frontier separately.
  have h₂ :
      frontier A ∪ frontier B ⊆ frontier (A ∪ B : Set X) := by
    intro x hx
    cases hx with
    | inl hxA =>
        -- `x` lies in the frontier of `A`.
        have hx_clA : x ∈ closure (A : Set X) := hxA.1
        have hx_not_intA : x ∉ interior (A : Set X) := hxA.2
        -- `interior A = A` since `A` is open.
        have h_intA : interior (A : Set X) = A := hA.interior_eq
        have hx_not_A : x ∉ A := by
          simpa [h_intA] using hx_not_intA
        -- Show that `x ∉ B`.
        have hx_not_B : x ∉ B := by
          intro hxB
          -- Every open neighbourhood of `x` meets `A`, contradiction with disjointness.
          have hForall := (mem_closure_iff).1 hx_clA
          have h_nonempty : ((B : Set X) ∩ A).Nonempty :=
            hForall B hB hxB
          have h_empty : (A ∩ B : Set X) = ∅ := hAB.eq_bot
          have : (A ∩ B : Set X).Nonempty := by
            -- Convert `B ∩ A` to `A ∩ B`.
            simpa [Set.inter_comm] using h_nonempty
          simpa [h_empty] using this
        -- Membership in the closure of the union.
        have hx_cl_union : x ∈ closure (A ∪ B : Set X) :=
          (closure_mono (by
            intro y hy; exact Or.inl hy)) hx_clA
        -- `A ∪ B` is open, hence its interior equals itself.
        have h_int_union : interior (A ∪ B : Set X) = A ∪ B := by
          have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
          simpa using h_open_union.interior_eq
        -- `x` is not in the interior of the union.
        have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := by
          have : x ∉ A ∪ B := by
            intro h_in
            cases h_in with
            | inl hA_in => exact hx_not_A hA_in
            | inr hB_in => exact hx_not_B hB_in
          simpa [h_int_union] using this
        exact ⟨hx_cl_union, hx_not_int_union⟩
    | inr hxB =>
        -- Symmetric argument with roles of `A` and `B` swapped.
        have hx_clB : x ∈ closure (B : Set X) := hxB.1
        have hx_not_intB : x ∉ interior (B : Set X) := hxB.2
        have h_intB : interior (B : Set X) = B := hB.interior_eq
        have hx_not_B : x ∉ B := by
          simpa [h_intB] using hx_not_intB
        -- Show `x ∉ A`.
        have hx_not_A : x ∉ A := by
          intro hxA
          have hForall := (mem_closure_iff).1 hx_clB
          have h_nonempty : ((A : Set X) ∩ B).Nonempty :=
            hForall A hA hxA
          have h_empty : (A ∩ B : Set X) = ∅ := hAB.eq_bot
          have : (A ∩ B : Set X).Nonempty := by
            simpa using h_nonempty
          simpa [h_empty] using this
        have hx_cl_union : x ∈ closure (A ∪ B : Set X) :=
          (closure_mono (by
            intro y hy; exact Or.inr hy)) hx_clB
        have h_int_union : interior (A ∪ B : Set X) = A ∪ B := by
          have h_open_union : IsOpen (A ∪ B) := IsOpen.union hA hB
          simpa using h_open_union.interior_eq
        have hx_not_int_union : x ∉ interior (A ∪ B : Set X) := by
          have : x ∉ A ∪ B := by
            intro h_in
            cases h_in with
            | inl hA_in => exact hx_not_A hA_in
            | inr hB_in => exact hx_not_B hB_in
          simpa [h_int_union] using this
        exact ⟨hx_cl_union, hx_not_int_union⟩
  exact subset_antisymm h₁ h₂

theorem Topology.closureInterior_inter_frontier_eq_closureInterior_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ frontier A = closure (interior A) \ interior A := by
  ext x
  constructor
  · intro hx
    -- `hx.1 : x ∈ closure (interior A)`
    -- `hx.2 : x ∈ frontier A = closure A \ interior A`
    exact ⟨hx.1, hx.2.2⟩
  · intro hx
    -- From `x ∈ closure (interior A)`,
    -- obtain `x ∈ closure A` via monotonicity of `closure`.
    have hx_closureA : x ∈ closure (A : Set X) := by
      have h_subset : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      exact h_subset hx.1
    -- Assemble the required membership in the intersection.
    exact ⟨hx.1, ⟨hx_closureA, hx.2⟩⟩



theorem Topology.frontier_inter_self_eq_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ∩ A = A \ interior A := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hfront, hA⟩
    exact ⟨hA, hfront.2⟩
  · intro hx
    rcases hx with ⟨hA, h_not_int⟩
    have h_cl : x ∈ closure (A : Set X) := subset_closure hA
    have h_front : x ∈ frontier (A : Set X) := ⟨h_cl, h_not_int⟩
    exact ⟨h_front, hA⟩

theorem Topology.frontier_closure_eq_closure_diff_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure (A : Set X)) =
      closure A \ interior (closure A) := by
  simpa using
    (Topology.frontier_eq_closure_diff_interior
      (A := closure A))

theorem Topology.disjoint_closureCompl_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Disjoint (closure (Aᶜ)) A := by
  -- From a general lemma we know `closure (Aᶜ) ⊆ (interior A)ᶜ`.
  have hsubset : closure (Aᶜ : Set X) ⊆ (A : Set X)ᶜ := by
    simpa [hA.interior_eq] using
      (Topology.closure_compl_subset_compl_interior (A := A))
  -- Translate this containment into the required disjointness.
  exact (Set.disjoint_left).2 (by
    intro x hx_cl hx_A
    have : x ∈ (Aᶜ : Set X) := hsubset hx_cl
    exact this hx_A)

theorem Topology.frontier_eq_closure_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = (∅ : Set X)) :
    frontier (A : Set X) = closure A := by
  simpa [frontier, h] using
    (by
      simp [frontier, h])

theorem Topology.closure_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B) := by
  -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields the result.
  have h_subset : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  exact closure_mono h_subset

theorem Topology.frontier_eq_compl_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (A : Set X)) :
    frontier (A : Set X) = (interior A)ᶜ := by
  classical
  -- `frontier A = closure A \ interior A`, and density gives `closure A = univ`.
  have h₁ : frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
    simpa [frontier, hA.closure_eq]
  -- Rewrite `univ \ interior A` as the complement of `interior A`.
  have h₂ : (Set.univ : Set X) \ interior A = (interior A)ᶜ := by
    ext x
    by_cases hx : x ∈ interior A <;> simp [hx]
  simpa [h₁, h₂]

theorem Topology.frontier_subset_compl_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ (interior A)ᶜ := by
  intro x hx
  exact hx.2

theorem Topology.interior_diff_eq_diff_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A \ B) = A \ closure B := by
  classical
  -- First inclusion: `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B) ⊆ A \ closure B := by
    intro x hxInt
    -- `x` lies in `A \ B`.
    have hxDiff : x ∈ A \ B := interior_subset hxInt
    have hxA    : x ∈ A := hxDiff.1
    -- Show `x ∉ closure B`.
    have hxNotCl : x ∉ closure B := by
      intro hxCl
      -- Any open neighbourhood of `x` meets `B`.
      have h_closure := (mem_closure_iff).1 hxCl
      -- The open set `interior (A \ B)` contains `x` and is disjoint from `B`,
      -- contradicting the previous statement.
      have h_nonempty : (interior (A \ B) ∩ B).Nonempty :=
        h_closure _ isOpen_interior hxInt
      rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
      have : y ∈ A \ B := interior_subset hyInt
      exact this.2 hyB
    exact ⟨hxA, hxNotCl⟩
  -- Second inclusion: `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B) := by
    -- The set `A \ closure B` is open.
    have hOpenDiff : IsOpen (A \ closure B) := by
      have hOpenCompl : IsOpen ((closure B)ᶜ) :=
        (isClosed_closure : IsClosed (closure B)).isOpen_compl
      simpa [Set.diff_eq] using hA.inter hOpenCompl
    -- And it is contained in `A \ B`.
    have hSubset : (A \ closure B : Set X) ⊆ A \ B := by
      intro x hx
      have hxNotB : x ∉ B := by
        intro hxB
        have : x ∈ closure B := subset_closure hxB
        exact hx.2 this
      exact ⟨hx.1, hxNotB⟩
    -- Use maximality of the interior.
    exact interior_maximal hSubset hOpenDiff
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hxInt
  -- From `hxInt : x ∈ interior (A \ B)`, we know `x ∈ A \ B`.
  have hxDiff : x ∈ A \ B := interior_subset hxInt
  -- Hence `x ∈ A`.
  have hxA : x ∈ A := hxDiff.1
  -- We claim that `x ∉ closure B`.
  have hxNotClB : x ∉ closure B := by
    intro hxClB
    -- Use the neighbourhood characterisation of closure.
    have h_cl := (mem_closure_iff).1 hxClB
    -- The open neighbourhood `interior (A \ B)` of `x` is disjoint from `B`,
    -- contradicting the definition of closure.
    have h_nonempty : ((interior (A \ B : Set X)) ∩ B).Nonempty := by
      have h_open : IsOpen (interior (A \ B : Set X)) := isOpen_interior
      exact h_cl _ h_open hxInt
    rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    have hyDiff : y ∈ A \ B := interior_subset hyInt
    exact (hyDiff.2 hyB).elim
  exact ⟨hxA, hxNotClB⟩

theorem Topology.frontier_closure_eq_empty_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    frontier (closure (A : Set X)) = (∅ : Set X) := by
  have h :=
    (Topology.frontier_closure_eq_closure_diff_interiorClosure (A := A))
  simpa [closure_closure, hOpen.interior_eq, Set.diff_self] using h

theorem Topology.frontier_eq_empty_iff_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  classical
  constructor
  · intro h_frontier
    -- From `frontier A = ∅` we deduce `closure A ⊆ interior A`.
    have h_subset : closure A ⊆ interior A := by
      intro x hx_cl
      by_contra hx_int
      have : x ∈ frontier (A : Set X) := ⟨hx_cl, hx_int⟩
      simpa [h_frontier] using this
    -- Hence `interior A ⊆ A ⊆ closure A ⊆ interior A`,
    -- so all three sets coincide.
    have h_int_eq : interior A = (A : Set X) := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        have hx_cl : x ∈ closure A := subset_closure hxA
        exact h_subset hx_cl
    have h_cl_eq : closure A = (A : Set X) := by
      apply subset_antisymm
      · intro x hx_cl
        exact (interior_subset : interior A ⊆ A) (h_subset hx_cl)
      · exact subset_closure
    -- Use these equalities to obtain openness and closedness.
    have h_open : IsOpen A := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have h_closed : IsClosed A := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact ⟨h_closed, h_open⟩
  · rintro ⟨h_closed, h_open⟩
    exact Topology.frontier_eq_empty_of_isClopen (A := A) h_closed h_open

theorem Topology.interior_frontier_eq_empty_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  classical
  -- First, rewrite the frontier of an open set.
  have h_front : frontier (A : Set X) = closure A \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  -- We show that the interior of `closure A \ A` is empty.
  have h_empty : interior (closure A \ A) = (∅ : Set X) := by
    apply (Set.eq_empty_iff_forall_not_mem).2
    intro x hx_int
    -- Obtain an open neighbourhood `U` of `x` contained in `closure A \ A`.
    rcases (mem_interior).1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
    -- Since `x ∈ interior (closure A \ A)`, it certainly lies in `closure A`.
    have hx_closureA : x ∈ closure (A : Set X) := by
      have : x ∈ closure A \ A :=
        (interior_subset : interior (closure A \ A) ⊆ closure A \ A) hx_int
      exact this.1
    -- Every neighbourhood of `x` meets `A`; apply this to `U`.
    have h_nonempty : (U ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_closureA U hU_open hxU
    rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩⟩
    -- But `U` is contained in `closure A \ A`, so `y ∉ A`, a contradiction.
    have hy_notA : y ∉ A := (hU_sub hyU).2
    exact hy_notA hyA
  -- Substitute back to finish the proof.
  simpa [h_front, h_empty]

theorem Topology.P3_of_interiorClosure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = A) : Topology.P3 (A := A) := by
  -- From the hypothesis we deduce that `A` is open.
  have h_open : IsOpen A := by
    simpa [h] using (isOpen_interior : IsOpen (interior (closure A)))
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) h_open

theorem Topology.closure_interClosure_eq_interClosure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  simpa using
    (Topology.closure_inter_eq_inter_of_closed
        (A := closure A) (B := closure B) hA hB)

theorem Topology.P1_of_boundary_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h : closure (A : Set X) \ interior A ⊆ closure (interior A)) :
    Topology.P1 (A := A) := by
  dsimp [Topology.P1] at *
  intro x hxA
  by_cases hxInt : x ∈ interior A
  · -- If `x` is in the interior of `A`, it is certainly in the closure of the interior.
    exact subset_closure hxInt
  · -- Otherwise, `x` lies on the boundary, which is assumed to be contained
    -- in `closure (interior A)`.
    have hx_boundary : x ∈ closure (A : Set X) \ interior A := by
      have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
      exact ⟨hx_closure, hxInt⟩
    exact h hx_boundary

theorem Topology.closure_union_interior_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A ∪ interior A) = closure A := by
  have h_union : (A ∪ interior A : Set X) = A := by
    ext x
    constructor
    · intro hx
      cases hx with
      | inl hxA      => exact hxA
      | inr hxIntA   => exact interior_subset hxIntA
    · intro hxA
      exact Or.inl hxA
  simpa [h_union]

theorem Topology.closure_union_six_eq {X : Type*} [TopologicalSpace X]
    (A B C D E F : Set X) :
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F) =
      closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪ closure F := by
  classical
  -- Regroup the big union so that we can apply the existing five-set lemma.
  have h₁ :
      (A ∪ B ∪ C ∪ D ∪ E ∪ F : Set X) = ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) := by
    simp [Set.union_assoc]
  -- Apply the lemma for five sets to the regrouped part.
  have h₂ :
      closure (A ∪ B ∪ C ∪ D ∪ E) =
        closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E :=
    Topology.closure_union_five_eq (A := A) (B := B) (C := C) (D := D) (E := E)
  -- Put everything together.
  calc
    closure (A ∪ B ∪ C ∪ D ∪ E ∪ F) =
        closure ((A ∪ B ∪ C ∪ D ∪ E) ∪ F) := by
          simpa [h₁]
    _ = closure (A ∪ B ∪ C ∪ D ∪ E) ∪ closure F := by
          simpa using
            (Topology.closure_union_eq
                (A := A ∪ B ∪ C ∪ D ∪ E) (B := F))
    _ = (closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E) ∪
          closure F := by
          simpa [h₂]
    _ = closure A ∪ closure B ∪ closure C ∪ closure D ∪ closure E ∪
          closure F := by
          simp [Set.union_assoc, Set.union_left_comm, Set.union_comm]



theorem Topology.frontier_interior_eq_frontier_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    frontier (interior (A : Set X)) = frontier A := by
  simpa [hA.interior_eq]

theorem Topology.frontier_inter_subset_frontier_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  rcases hx with ⟨hx_clAB, hx_not_intAB⟩
  -- From the closure of an intersection to the intersection of the closures.
  have h_cl_subset :
      closure (A ∩ B : Set X) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  have hx_clA : x ∈ closure A := (h_cl_subset hx_clAB).1
  have hx_clB : x ∈ closure B := (h_cl_subset hx_clAB).2
  -- Express the interior of an intersection.
  have h_int_eq :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)
  -- Case analysis on membership in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x` would be in `interior (A ∩ B)`.
    have h_not_intB : x ∉ interior B := by
      intro hIntB
      have : x ∈ interior (A ∩ B : Set X) := by
        have : x ∈ interior A ∩ interior B := ⟨hIntA, hIntB⟩
        simpa [h_int_eq] using this
      exact hx_not_intAB this
    -- Assemble membership in `frontier B ∩ closure A`.
    have hx_frontierB : x ∈ frontier B := ⟨hx_clB, h_not_intB⟩
    exact Or.inr ⟨hx_frontierB, hx_clA⟩
  · -- Otherwise, `x ∉ interior A`, so `x` is in `frontier A ∩ closure B`.
    have h_not_intA : x ∉ interior A := hIntA
    have hx_frontierA : x ∈ frontier A := ⟨hx_clA, h_not_intA⟩
    exact Or.inl ⟨hx_frontierA, hx_clB⟩

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) = A ∪ frontier A := by
  classical
  ext x
  constructor
  · intro hx_cl
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · -- `x` is in `closure A` but not in `A`; hence it lies in the frontier.
      have hx_not_int : x ∉ interior (A : Set X) := by
        intro hx_int
        exact hxA (interior_subset hx_int)
      exact Or.inr ⟨hx_cl, hx_not_int⟩
  · intro hx_union
    cases hx_union with
    | inl hxA      => exact subset_closure hxA
    | inr hxFront  => exact hxFront.1

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (interior A ∩ B) ⊆ closure (A ∩ B) := by
  -- `interior A` is contained in `A`, hence their intersection with `B`
  -- sits inside `A ∩ B`.
  have h_subset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨interior_subset hx.1, hx.2⟩
  -- Taking closures preserves this inclusion.
  exact closure_mono h_subset

theorem Topology.closureInterior_union_interiorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∪ interior (closure A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl h_closureInt =>
      exact (Topology.closureInterior_subset_closure (A := A)) h_closureInt
  | inr h_interiorCl =>
      exact (Topology.interiorClosure_subset_closure (A := A)) h_interiorCl

theorem Topology.frontier_compl_swap {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (A : Set X) = frontier (Aᶜ) := by
  simpa using (frontier_compl (A := A)).symm

theorem Topology.frontier_diff_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A \ B : Set X) ⊆ frontier A ∪ frontier B := by
  classical
  intro x hx
  -- Rewrite the difference as an intersection with the complement.
  have hx' : x ∈ frontier (A ∩ Bᶜ : Set X) := by
    simpa [Set.diff_eq] using hx
  -- Apply the lemma for intersections.
  have hStep :=
    (Topology.frontier_inter_subset_union_frontier
        (A := A) (B := Bᶜ)) hx'
  -- Convert the frontier of `Bᶜ` back to `B` using `frontier_compl`.
  cases hStep with
  | inl hA =>
      exact Or.inl hA
  | inr hBcompl =>
      have hB : x ∈ frontier (B : Set X) := by
        simpa [frontier_compl (A := B)] using hBcompl
      exact Or.inr hB

theorem Topology.frontier_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior (A : Set X))) ⊆ frontier A := by
  -- `frontier (closure (interior A)) ⊆ frontier (interior A)`
  have h₁ :
      frontier (closure (interior (A : Set X))) ⊆
        frontier (interior (A : Set X)) :=
    Topology.frontier_closure_subset_frontier (A := interior A)
  -- `frontier (interior A) ⊆ frontier A`
  have h₂ :
      frontier (interior (A : Set X)) ⊆ frontier A :=
    Topology.frontier_interior_subset_frontier (A := A)
  -- Combine the two inclusions.
  exact subset_trans h₁ h₂

theorem Topology.closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier (A : Set X)) ⊆ closure A := by
  -- `frontier A` is contained in `closure A`.
  have h : frontier (A : Set X) ⊆ closure A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  have h' : closure (frontier (A : Set X)) ⊆ closure (closure A) := closure_mono h
  simpa [closure_closure] using h'

theorem Topology.interior_union_frontier_eq_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier A = closure A := by
  classical
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- Points of `interior A` are certainly in `closure A`.
        exact subset_closure (interior_subset hxInt)
    | inr hxFront =>
        -- The first component of `frontier` membership is `closure A`.
        exact hxFront.1
  · intro hxCl
    -- Split depending on whether `x` lies in `interior A`.
    by_cases hxInt : x ∈ interior (A : Set X)
    · exact Or.inl hxInt
    · exact Or.inr ⟨hxCl, hxInt⟩

theorem Topology.closureInteriors_inter_subset_closureInteriorUnion
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  -- `interior A` is contained in `interior (A ∪ B)`.
  have h_intA_subset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := by
      intro y hy; exact Or.inl hy
    exact interior_mono h_sub
  -- Hence their closures satisfy the same inclusion.
  have h_clA_subset :
      closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_intA_subset
  -- Apply the inclusion to the first component of `hx`.
  exact h_clA_subset hx.1

theorem Topology.interior_frontier_eq_empty_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (frontier (A : Set X)) = (∅ : Set X) := by
  -- First, rewrite the frontier of a closed set.
  have hFrontier : frontier (A : Set X) = A \ interior A := by
    simpa [frontier, hA_closed.closure_eq]
  -- Show that the interior of `A \ interior A` is empty.
  have hEmpty : interior (A \ interior A : Set X) = (∅ : Set X) := by
    apply (Set.eq_empty_iff_forall_not_mem).2
    intro x hx
    -- Obtain an open neighbourhood `U` of `x` contained in `A \ interior A`.
    rcases (mem_interior).1 hx with ⟨U, hU_sub, hU_open, hxU⟩
    -- From the inclusion, `U ⊆ A`.
    have hU_subA : U ⊆ (A : Set X) := by
      intro y hy
      exact (hU_sub hy).1
    -- Hence `U ⊆ interior A`, by maximality of the interior.
    have hU_subIntA : U ⊆ interior A := interior_maximal hU_subA hU_open
    -- Therefore `x ∈ interior A`, contradicting `x ∉ interior A`.
    have hxIntA : x ∈ interior A := hU_subIntA hxU
    have hxNotIntA : x ∉ interior A := (hU_sub hxU).2
    exact hxNotIntA hxIntA
  -- Combine the two equalities.
  simpa [hFrontier] using hEmpty

theorem Topology.closureInterior_inter_frontier_eq_frontierInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ frontier A = frontier (interior A) := by
  calc
    closure (interior A) ∩ frontier A
        = closure (interior A) \ interior A := by
          simpa using
            (Topology.closureInterior_inter_frontier_eq_closureInterior_diff_interior
                (A := A))
    _ = frontier (interior A) := by
          simpa using
            (Topology.frontier_interior_eq_closureInterior_diff_interior
                (A := A)).symm

theorem Topology.interior_union_frontier_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier A ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hx_int =>
      -- Points of `interior A` are, in particular, in `A`
      -- and hence lie in `closure A`.
      exact subset_closure (interior_subset hx_int)
  | inr hx_frontier =>
      -- By definition of the frontier, its points already
      -- belong to `closure A`.
      exact hx_frontier.1



theorem Topology.closure_inter_frontier_eq_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ frontier A = frontier A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨hx.1, hx⟩

theorem Topology.interior_eq_self_diff_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) = A \ frontier A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx_int
    have hxA : x ∈ A := interior_subset hx_int
    have h_not_front : x ∉ frontier (A : Set X) := by
      intro h_front
      exact h_front.2 hx_int
    exact ⟨hxA, h_not_front⟩
  · intro x hx_diff
    rcases hx_diff with ⟨hxA, h_not_front⟩
    by_contra h_not_int
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    have hx_front : x ∈ frontier (A : Set X) := ⟨hx_cl, h_not_int⟩
    exact h_not_front hx_front

theorem Topology.closure_eq_closureInterior_union_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) = closure (interior A) ∪ frontier A := by
  classical
  ext x
  constructor
  · intro hx_cl
    by_cases hx_clInt : x ∈ closure (interior A)
    · exact Or.inl hx_clInt
    ·
      -- Since `x ∉ interior A` and `x ∈ closure A`, it lies in the frontier.
      have hx_not_int : x ∉ interior A := by
        intro hx_int
        have : x ∈ closure (interior A) := subset_closure hx_int
        exact hx_clInt this
      exact Or.inr ⟨hx_cl, hx_not_int⟩
  · intro hx_union
    cases hx_union with
    | inl hx_clInt =>
        have h_subset : closure (interior A) ⊆ closure A :=
          closure_mono (interior_subset : interior A ⊆ A)
        exact h_subset hx_clInt
    | inr hx_front =>
        exact hx_front.1

theorem Topology.frontier_subset_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B : Set X) ⊆ closure A ∪ closure B := by
  intro x hx
  -- From `hx`, obtain membership in the closure of `A ∪ B`.
  have hx_closure : x ∈ closure (A ∪ B : Set X) := hx.1
  -- Rewrite the closure of the union using an existing lemma.
  have h_union : closure (A ∪ B : Set X) = closure A ∪ closure B :=
    Topology.closure_union_eq (A := A) (B := B)
  -- Use the equality to convert membership.
  simpa [h_union] using hx_closure

theorem Topology.disjoint_interior_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    Disjoint (interior (A : Set X)) (frontier A) := by
  -- We use `Set.disjoint_left`, which asks to prove that no element
  -- can belong to both sets simultaneously.
  exact (Set.disjoint_left).2 (by
    intro x hxInt hxFront
    -- From `hxFront : x ∈ frontier A = closure A \ interior A`
    -- we have `hxFront.2 : x ∉ interior A`, contradicting `hxInt`.
    exact hxFront.2 hxInt)

theorem Topology.closure_frontier_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier (A : Set X)) = closure A \ interior A := by
  calc
    closure (frontier (A : Set X))
        = frontier (A : Set X) := by
          simpa using (Topology.closureFrontier_eq_self (A := A))
    _ = closure A \ interior A := by
          simpa using
            (Topology.frontier_eq_closure_diff_interior (A := A))

theorem Topology.frontier_frontier_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier (A : Set X)) ⊆ frontier A := by
  intro x hx
  have hx_cl : x ∈ closure (frontier (A : Set X)) := hx.1
  have h_cl_eq :
      closure (frontier (A : Set X)) = frontier (A : Set X) :=
    (isClosed_frontier : IsClosed (frontier (A : Set X))).closure_eq
  simpa [h_cl_eq] using hx_cl

theorem frontier_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (A : Set X)) ⊆ closure A := by
  have h₁ :
      frontier (closure (A : Set X)) ⊆ frontier (A : Set X) :=
    Topology.frontier_closure_subset_frontier (A := A)
  have h₂ :
      frontier (A : Set X) ⊆ closure A :=
    Topology.frontier_subset_closure (A := A)
  exact Set.Subset.trans h₁ h₂

theorem Topology.closure_diff_frontier_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (A : Set X) \ frontier A = A := by
  classical
  -- Use the description of the frontier for open sets.
  have h_front : frontier (A : Set X) = closure A \ A :=
    Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  -- First, show `closure A \ frontier A ⊆ A`.
  have h_sub : closure A \ frontier A ⊆ A := by
    intro x hx
    rcases hx with ⟨hx_cl, hx_not_front⟩
    by_cases hxa : x ∈ A
    · exact hxa
    · have : x ∈ closure A \ A := ⟨hx_cl, hxa⟩
      have : x ∈ frontier (A : Set X) := by
        simpa [h_front] using this
      exact (hx_not_front this).elim
  -- Next, show `A ⊆ closure A \ frontier A`.
  have h_sup : (A : Set X) ⊆ closure A \ frontier A := by
    intro x hxA
    have hx_cl : x ∈ closure A := subset_closure hxA
    have hx_not_front : x ∉ frontier (A : Set X) := by
      intro hfront
      have : x ∈ closure A \ A := by
        simpa [h_front] using hfront
      exact this.2 hxA
    exact ⟨hx_cl, hx_not_front⟩
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h_sub h_sup

theorem closure_diff_subset_left {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set difference `A \ B` is obviously contained in `A`.
  have hsubset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset

theorem Topology.isClosed_iff_frontier_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ frontier (A : Set X) ⊆ A := by
  classical
  constructor
  · intro hClosed
    exact Topology.frontier_subset_of_isClosed (A := A) hClosed
  · intro hSubset
    -- First, show `closure A ⊆ A`.
    have h_closure_subset : closure (A : Set X) ⊆ A := by
      intro x hx_cl
      -- Using `closure A = A ∪ frontier A`.
      have hx_union : x ∈ (A : Set X) ∪ frontier (A : Set X) := by
        simpa [Topology.closure_eq_self_union_frontier (A := A)] using hx_cl
      cases hx_union with
      | inl hA       => exact hA
      | inr hFront   => exact hSubset hFront
    -- Hence `closure A = A`.
    have h_eq : closure (A : Set X) = A :=
      Set.Subset.antisymm h_closure_subset subset_closure
    -- Conclude that `A` is closed.
    have h_closed_closure : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_eq] using h_closed_closure

theorem Topology.inter_interior_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ frontier A = (∅ : Set X) := by
  classical
  -- We show that no point can belong to the intersection.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_int, hx_front⟩
  -- `hx_front.2` states that `x ∉ interior A`, contradicting `hx_int`.
  exact (hx_front.2) hx_int

theorem interior_inter_left_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B) = interior A ∩ B := by
  have h := Topology.interior_inter_eq_inter (A := A) (B := B)
  simpa [hB.interior_eq] using h

theorem Topology.frontier_union_three_subset_union_frontier
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    frontier (A ∪ B ∪ C : Set X) ⊆ frontier A ∪ frontier B ∪ frontier C := by
  intro x hx
  -- Reassociate the union to use the two–set lemma twice.
  have hx₁ : x ∈ frontier ((A ∪ B) ∪ C : Set X) := by
    simpa [Set.union_assoc] using hx
  -- First application: break the frontier of `(A ∪ B) ∪ C`.
  have h₁ : x ∈ frontier (A ∪ B) ∪ frontier C :=
    (frontier_union_subset (A := A ∪ B) (B := C)) hx₁
  cases h₁ with
  | inl hAB =>
      -- Second application: break the frontier of `A ∪ B`.
      have h₂ : x ∈ frontier A ∪ frontier B :=
        (frontier_union_subset (A := A) (B := B)) hAB
      cases h₂ with
      | inl hA =>
          -- `x ∈ frontier A`
          exact Or.inl (Or.inl hA)
      | inr hB =>
          -- `x ∈ frontier B`
          exact Or.inl (Or.inr hB)
  | inr hC =>
      -- `x ∈ frontier C`
      exact Or.inr hC

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed A) (h_dense : Dense (A : Set X)) :
    A = (Set.univ : Set X) := by
  -- For closed sets, the closure is the set itself.
  have h_closure_self : closure (A : Set X) = A := h_closed.closure_eq
  -- For dense sets, the closure is the whole space.
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := h_dense.closure_eq
  -- Combine the two equalities.
  simpa [h_closure_self] using h_closure_univ

theorem Topology.frontier_inter_eq_union_frontier_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    frontier (A ∩ B : Set X) =
      (frontier A ∩ B) ∪ (frontier B ∩ A) := by
  classical
  -- Useful rewrites for frontiers of closed sets.
  have hFrontA :
      frontier (A : Set X) = A \ interior A :=
    (Topology.frontier_eq_diff_interior_of_isClosed (A := A) hA)
  have hFrontB :
      frontier (B : Set X) = B \ interior B :=
    (Topology.frontier_eq_diff_interior_of_isClosed (A := B) hB)
  have hClosedAB : IsClosed (A ∩ B : Set X) := IsClosed.inter hA hB
  have hFrontAB :
      frontier (A ∩ B : Set X) = (A ∩ B) \ interior (A ∩ B) :=
    (Topology.frontier_eq_diff_interior_of_isClosed
      (A := A ∩ B) hClosedAB)
  -- The interior of an intersection.
  have hIntAB :
      interior (A ∩ B : Set X) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (A := A) (B := B)

  -- Establish the set equality.
  ext x; constructor
  · -- `→`  direction.
    intro hx
    -- Rewrite membership in `frontier (A ∩ B)`.
    have hxAB : x ∈ (A ∩ B) \ interior (A ∩ B) := by
      simpa [hFrontAB] using hx
    rcases hxAB with ⟨⟨hxA, hxB⟩, hNotIntAB⟩
    -- `x` fails to lie in `interior A ∩ interior B`.
    have hNotBoth : x ∉ interior A ∩ interior B := by
      simpa [hIntAB] using hNotIntAB
    -- Hence, `¬ x ∈ interior A ∧ x ∈ B` or `¬ x ∈ interior B ∧ x ∈ A`.
    have hCase : x ∉ interior A ∨ x ∉ interior B := by
      by_cases hIntA : x ∈ interior A
      · right
        intro hIntB; exact hNotBoth ⟨hIntA, hIntB⟩
      · left; exact hIntA
    cases hCase with
    | inl hNotIntA =>
        -- Build membership in `frontier A ∩ B`.
        have hxFrontA : x ∈ frontier A := by
          have : x ∈ A \ interior A := ⟨hxA, hNotIntA⟩
          simpa [hFrontA] using this
        exact Or.inl ⟨hxFrontA, hxB⟩
    | inr hNotIntB =>
        -- Build membership in `frontier B ∩ A`.
        have hxFrontB : x ∈ frontier B := by
          have : x ∈ B \ interior B := ⟨hxB, hNotIntB⟩
          simpa [hFrontB] using this
        exact Or.inr ⟨hxFrontB, hxA⟩
  · -- `←` direction.
    intro hx
    cases hx with
    | inl hLeft =>
        rcases hLeft with ⟨hxFrontA, hxB⟩
        -- Extract data from `hxFrontA`.
        have hxA : x ∈ A := by
          have : x ∈ A \ interior A := by
            simpa [hFrontA] using hxFrontA
          exact this.1
        have hNotIntA : x ∉ interior A := by
          have : x ∈ A \ interior A := by
            simpa [hFrontA] using hxFrontA
          exact this.2
        -- Show `x ∉ interior (A ∩ B)`.
        have hNotIntAB : x ∉ interior (A ∩ B) := by
          intro hIntAB
          have : x ∈ interior A ∩ interior B := by
            simpa [hIntAB] using hIntAB
          exact hNotIntA this.1
        -- Conclude membership in `frontier (A ∩ B)`.
        have : x ∈ (A ∩ B) \ interior (A ∩ B) :=
          ⟨⟨hxA, hxB⟩, hNotIntAB⟩
        simpa [hFrontAB] using this
    | inr hRight =>
        rcases hRight with ⟨hxFrontB, hxA⟩
        -- Extract data from `hxFrontB`.
        have hxB : x ∈ B := by
          have : x ∈ B \ interior B := by
            simpa [hFrontB] using hxFrontB
          exact this.1
        have hNotIntB : x ∉ interior B := by
          have : x ∈ B \ interior B := by
            simpa [hFrontB] using hxFrontB
          exact this.2
        -- Show `x ∉ interior (A ∩ B)`.
        have hNotIntAB : x ∉ interior (A ∩ B) := by
          intro hIntAB
          have : x ∈ interior A ∩ interior B := by
            simpa [hIntAB] using hIntAB
          exact hNotIntB this.2
        -- Conclude membership in `frontier (A ∩ B)`.
        have : x ∈ (A ∩ B) \ interior (A ∩ B) :=
          ⟨⟨hxA, hxB⟩, hNotIntAB⟩
        simpa [hFrontAB] using this

theorem Topology.isOpen_iff_frontier_subset_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (A : Set X) ↔ frontier (A : Set X) ⊆ Aᶜ := by
  classical
  constructor
  · intro hA_open
    -- For an open set, the frontier is `closure A \ A`, whence the claim.
    intro x hx_front
    have h_frontier :
        frontier (A : Set X) = closure A \ A :=
      Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA_open
    have : x ∈ closure A \ A := by
      simpa [h_frontier] using hx_front
    exact this.2
  · intro h_frontier_sub
    -- Show `A ⊆ interior A`; the reverse inclusion is automatic.
    have h_eq_int : interior (A : Set X) = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        by_contra hx_not_int
        -- Then `x` lies in the frontier, contradicting the assumption.
        have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
        have hx_front : x ∈ frontier (A : Set X) := ⟨hx_cl, hx_not_int⟩
        have : x ∈ (Aᶜ : Set X) := h_frontier_sub hx_front
        exact this hxA
    -- An interior equals the set itself iff the set is open.
    simpa [h_eq_int] using (isOpen_interior : IsOpen (interior A))

theorem Topology.frontier_subset_compl_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    frontier (A : Set X) ⊆ Aᶜ := by
  simpa using
    ((Topology.isOpen_iff_frontier_subset_compl (A := A)).1 hA)