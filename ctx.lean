namespace ctx
    @[inline, reducible] def pipe {A B: Sort _} (a: A) (f: A → B): B := f a
    infix ` ↦ `:50 := pipe

    -- converting to continuation passing style
    def of {A X: Sort _} (a: A): (A → X) → X :=
        λ xa: A → X,
        xa a

    def uncurry {A B X: Sort _} (fx: ((A → B) → X) → X): A → (B → X) → X :=
        begin
            intros a xb,
            apply fx,
            intro f,
            apply xb,
            apply f,
            exact a,
        end

    def of_func {A B X: Sort _} (f: A → B): A → (B → X) → X :=
        uncurry (of f)

    def curry.of_dne {A B C X: Sort _} (bdne: ((B → X) → X) → C) (fx: A → (B → X) → X): ((A → C) → X) → X :=
        begin
            intro xf,
            apply xf,
            intro a,
            let bxx: (B → X) → X := fx a,
            apply bdne,
            exact bxx,
        end

    -- classical logic equivalents in ctx style
    def dne {A X: Sort _} (xxa: (A → X) → X) (ctx: A → X): X :=
        xxa ctx

    theorem dne.of_prop {X: Sort _} {P: Prop} (xxp: (P → X) → X) (ctx: P → X): X :=
        dne xxp ctx

    def lem.of_sum {A X: Type _} (ctx: A ⊕ (A → X) → X): X :=
        begin
            apply ctx,
            apply sum.inr,
            intro a,
            apply ctx,
            apply sum.inl,
            exact a,
        end

    theorem lem.of_or {X: Sort _} {P: Prop} (ctx: P ∨ (P → X) → X): X :=
        begin
            apply ctx,
            right,
            intro p,
            apply ctx,
            left,
            exact p,
        end

    -- conversion between functions to X and ¬X
    def of_not {A X: Sort _} (na: ¬A): A → X :=
        begin
            intro a,
            apply false.elim,
            apply na,
            exact a,
        end

    theorem of_not.of_prop {X: Sort _} {P: Prop} (np: ¬P): P → X :=
        of_not np

    def inner_to_not {A X: Sort _} (xxa: (A → X) → X): ¬A → X :=
        λ na: A → false,
        let f: A → X := of_not na in
        xxa f

    theorem inner_to_not.of_prop {X: Sort _} {P: Prop} (xxp: (P → X) → X): ¬P → X :=
        inner_to_not xxp

    -- we get more power if we use a fixed return value X and assume (A → X) → ¬A
    namespace fixed_output
        constant X: Sort _
        axiom to_not {A: Sort _}: (A → X) → ¬A

        theorem to_not.of_prop {P: Prop} (xp: P → X): ¬P :=
            to_not xp

        def to_double_neg {A: Sort _} (xxa: (A → X) → X): ¬¬A :=
            xxa ↦ inner_to_not ↦ to_not

        noncomputable def curry {A B: Sort _} (fx: A → (B → X) → X): ((A → ¬¬B) → X) → X :=
            curry.of_dne to_double_neg fx

        noncomputable def of_double_neg {A: Sort _} (nna: ¬¬A): (A → X) → X :=
            λ xa: A → X,
            let na: A → false := to_not xa in
            let bot: false := nna na in
            false.elim bot
    end fixed_output
end ctx
