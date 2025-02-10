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

## Given Barendregt's definition of saturated sets, what is the largest staturated set?

# Proof Goal
Prove that SN is the largest saturated set. 

## Definitions 

### Definition 4.3.1
1. $\text{SN} = \{M \in \Lambda \mid M \text{ is strongly normalizing}\}$

### Definition 4.3.2
1. A subset $X \subseteq \text{SN}$ is called saturated if:
   
   (a) $\forall n \geq 0$ $\forall R_1,\ldots,R_n \in \text{SN}$ $x\vec{R} \in X$,
       where $x$ is any term variable;
   
   (b) $\forall n \geq 0$ $\forall R_1,\ldots,R_n \in \text{SN}$ $\forall Q \in \text{SN}$
       
       $P[x := Q]\vec{R} \in X \Rightarrow (\lambda x.P)Q\vec{R} \in X$
       

2. $\text{SAT} = \{X \subseteq \Lambda \mid X \text{ is saturated}\}$

### Lemma 4.3.3
1. $\text{SN} \in \text{SAT}$

## Proof

We will prove that SN is the largest saturated set by showing:
1. SN is saturated
2. Every saturated set must be a subset of SN
3. Therefore, SN must be the largest set. 

### 1: SN is Saturated
By Lemma 4.3.3.1, we know that $\text{SN} \in \text{SAT}$, which directly tells us that SN is saturated.

### 2: Every Saturated Set is a Subset of SN
From Definition 4.3.2.1, a saturated set $X$ is defined as "a subset $X \subseteq \text{SN}$" satisfying conditions (a) and (b). Therefore, by definition, any saturated set must be contained within SN.

### 3: SN is the Largest Saturated Set

From **Definition 4.3.2**, any saturated set $X$ must be a subset of $\text{SN}$, meaning:

$X \subseteq \text{SN}, \quad \forall X \in \text{SAT}$.

Since $\text{SN}$ is itself a saturated set (by **Lemma 4.3.3**), it follows that it is the **largest** saturated set, meaning no saturated set can properly contain $\text{SN}$.

Thus, $\text{SN}$ is the largest element in $\text{SAT}$.

$\square$