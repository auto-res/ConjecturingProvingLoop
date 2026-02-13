

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro h
    exact (P2_prod_swap (A := A) (B := B)) h
  · intro h
    exact (P2_prod_swap (X := Y) (Y := X) (A := B) (B := A)) h

theorem P3_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (Set.prod A A) ↔ P3 A := by
  constructor
  · intro hProd
    -- we prove `P3 A`
    unfold P3 at hProd ⊢
    intro x hxA
    -- the point `(x, x)` lies in `A ×ˢ A`
    have hx_pair : (x, x) ∈ Set.prod A A := by
      exact ⟨hxA, hxA⟩
    -- hence it belongs to the open set appearing in `P3`
    have hxx :
        (x, x) ∈ interior (closure (Set.prod A A)) := hProd hx_pair
    -- the open neighbourhood provided by `P3`
    have hO_open :
        IsOpen (interior (closure (Set.prod A A)) : Set (X × X)) :=
      isOpen_interior
    have hO_nhds :
        (interior (closure (Set.prod A A)) : Set (X × X)) ∈ nhds (x, x) :=
      hO_open.mem_nhds hxx
    -- obtain rectangular neighbourhoods
    rcases (mem_nhds_prod_iff).1 hO_nhds with
      ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
    rcases (mem_nhds_iff).1 hU_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
    rcases (mem_nhds_iff).1 hV_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
    -- define the open neighbourhood `W` of `x`
    let W : Set X := U₀ ∩ V₀
    have hW_open : IsOpen (W : Set X) := hU₀_open.inter hV₀_open
    have hxW : x ∈ W := by
      dsimp [W]; exact ⟨hxU₀, hxV₀⟩
    -- `U₀ ×ˢ V₀` is contained in the big open set
    have hProdSub :
        (Set.prod U₀ V₀ : Set (X × X)) ⊆
          interior (closure (Set.prod A A)) :=
      (Set.prod_mono hU₀_sub hV₀_sub).trans hUV_sub
    -- every point of `W` is in the closure of `A`
    have hW_subset : (W : Set X) ⊆ closure A := by
      intro y hyW
      -- `(y, y)` belongs to `U₀ ×ˢ V₀ ⊆ interior (closure (A × A))`
      have hy_pair :
          (y, y) ∈ interior (closure (Set.prod A A)) := by
        have : (y, y) ∈ Set.prod U₀ V₀ := by
          exact ⟨hyW.1, hyW.2⟩
        exact hProdSub this
      -- hence `(y, y)` is in the closure of `A × A`
      have hy_pair_cl :
          (y, y) ∈ closure (Set.prod A A) := interior_subset hy_pair
      -- use the neighbourhood characterization of the closure
      apply (mem_closure_iff).2
      intro S hS hyS
      -- consider `S ×ˢ S`
      let SS : Set (X × X) := Set.prod S S
      have hSS_open : IsOpen (SS : Set (X × X)) := hS.prod hS
      have h_pair_SS : (y, y) ∈ SS := by
        exact ⟨hyS, hyS⟩
      -- intersect with `A × A`
      have hNonempty :
          (SS ∩ Set.prod A A).Nonempty :=
        (mem_closure_iff).1 hy_pair_cl SS hSS_open h_pair_SS
      rcases hNonempty with ⟨⟨a, b⟩, hmem⟩
      have hSSmem : (a, b) ∈ SS := hmem.1
      have hABmem : (a, b) ∈ Set.prod A A := hmem.2
      -- `a` lies in `S ∩ A`
      exact
        ⟨a, hSSmem.1, hABmem.1⟩
    -- `W` is an open nbhd of `x` contained in `closure A`
    have hInt := interior_maximal hW_subset hW_open
    exact hInt hxW
  · intro hA
    -- the reverse implication follows from `P3_prod`
    simpa using (P3_prod (A := A) (B := A) hA hA)

theorem P1_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = closure A → P1 A := by
  intro hEq
  exact (P1_iff_closure_eq (A := A)).2 hEq

theorem P3_of_open_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f) {A : Set X} : P3 A → P3 (f '' A) := by
  intro hP3
  -- expand the definition of `P3`
  dsimp [P3] at hP3 ⊢
  -- we have to prove:  f '' A ⊆ interior (closure (f '' A))
  intro y hyImage
  -- choose a preimage point
  rcases hyImage with ⟨x, hxA, rfl⟩
  -- use the hypothesis `P3 A`
  have hxInt : (x : X) ∈ interior (closure A) := hP3 hxA
  ------------------------------------------------------------------
  -- 1.  the auxiliary open set  O := f '' interior (closure A)
  ------------------------------------------------------------------
  have hO_open : IsOpen (f '' interior (closure A) : Set Y) := by
    have h_src_open : IsOpen (interior (closure A) : Set X) := isOpen_interior
    exact hopen _ h_src_open
  ------------------------------------------------------------------
  -- 2.  show   O ⊆ closure (f '' A)
  ------------------------------------------------------------------
  have hO_subset : (f '' interior (closure A) : Set Y) ⊆ closure (f '' A) := by
    intro z hz
    rcases hz with ⟨x', hx'Int, rfl⟩
    -- `x'` lies in `closure A`
    have hx'Cl : (x' : X) ∈ closure A := interior_subset hx'Int
    -- we prove that `f x'` is in the closure of `f '' A`
    have : (f x' : Y) ∈ closure (f '' A) := by
      -- neighbourhood criterion for the closure
      apply (mem_closure_iff).2
      intro V hV hVfx
      -- the preimage of `V` is open
      have h_pre_open : IsOpen (f ⁻¹' V) := hV.preimage hf
      -- `x'` belongs to this preimage
      have hx'_pre : x' ∈ f ⁻¹' V := by
        simpa using hVfx
      -- since `x' ∈ closure A`, the intersection meets `A`
      have h_nonempty : ((f ⁻¹' V) ∩ A).Nonempty := by
        have h := (mem_closure_iff).1 hx'Cl (f ⁻¹' V) h_pre_open hx'_pre
        simpa [Set.inter_comm] using h
      rcases h_nonempty with ⟨x₁, hx₁_pre, hx₁A⟩
      -- provide the required witness in `V ∩ f '' A`
      exact
        ⟨f x₁, ⟨by
          simpa using hx₁_pre,
          ⟨x₁, hx₁A, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- 3.  `f x` lies in the interior of the target closure
  ------------------------------------------------------------------
  have hfx_mem_O : (f x : Y) ∈ f '' interior (closure A) := ⟨x, hxInt, rfl⟩
  have h_result : (f x : Y) ∈ interior (closure (f '' A)) :=
    (interior_maximal hO_subset hO_open) hfx_mem_O
  exact h_result