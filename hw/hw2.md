## HW 2
## Exercise 2 from Bob Harper's How to (Re)Invent Tait's Method
# **Proof of Hereditary Termination using Negative Formulation**
# Proof Goal

We prove the **fundamental theorem of hereditary termination**:

For all M, if Γ ⊢ M : A, then HT_A(M).

where hereditary termination is defined using the **negative formulation**.

# Theorem (Termination with Negative Formulation)
For closed programs of answer type, we use the following negative formulation of hereditary termination:

HT_(A₁×A₂)(M) iff HT_A₁(M·1) and HT_A₂(M·2)
HT_(A₁→A₂)(M) iff HT_A₁(M₁) implies HT_A₂(ap(M;M₁))

For answer type:
HT_ans(M) iff M →* yes or M →* no

## Rules Used
### Product Rules
- LFT-PAIR: ⟨M₁,M₂⟩·1 →* M₁
- RHT-PAIR: ⟨M₁,M₂⟩·2 →* M₂

### Application Rules
- APP-LAM: ap(λ(x.M);M₂) → [M₂/x]M

### Contextual Rules
- If M →* M', then M·1 →* M'·1
- If M →* M', then M·2 →* M'·2
- If M₁ →* M₁', then ap(M₁;M₂) →* ap(M₁';M₂)

## Proof
 We prove that if M : ans is a closed term, then M →* yes or M →* no.

**Case 1 (Base ans):** If M is yes or no, immediate.

**Case 2 (Products):** If M : ans contains a product subterm:
- For projections M·1 or M·2, by LFT-PAIR/RHT-PAIR rules, these reduce to their components
- By preservation, these components must also be of type ans 
- By induction on the typing derivation, these components reduce to yes or no

**Case 3 (Functions):** If M : ans contains function application:
- For ap(M₁;M₂), by APP-LAM rule and preservation, this reduces to a term still of type ans
- By induction, this reduced term must evaluate to yes or no
∎

