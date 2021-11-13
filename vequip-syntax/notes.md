# What's to be done

1. Formalize the syntax and admissible rules
2. Initiality theorem for virtual equipments
3. Internal category theory
4. Synthetic category theory
5. implementation as a proof assistant
   - formalization of the module system

# Internal Categories as a syntactic construction

Because the monads and modules construction is an endomorphism VEquip
-> VEquip, we can express it as a translation from 

## Tensor and Cotensor
Tensor is written as

R[a,b] ⊙ Q[b,c] = exists b. R[a,b] ⊗ Q[b,c]
and it's subject to the equation that for any

(b,r,q) and (b',r',q') and f : b -> b',
if fr = r' and q'f = q then

    (b,r,q) = (b',r',q')

To express this we would need some kind of quotient construction.

Could be written as a co-equalizer of

    exists b,b'. R[a,b] ⊙ B[b,b'] ⊙ Q[b',c] => exists b. R[a,b]  ⊙ Q[b',c]

So if we add co-equalizers/pushouts we can define this internally.

(Contravariant) Cotensor is

R[a,b] ▹ P[a,c] := forall a. R[a,b] -> P[a,c]
but we restrict to the subset that is uniform in a in that for any

(a,r) and (a',r'), and alpha : a -> a' such that r'alpha = r
then for any phi : forall a. R[a,b] -> P[a,c]

    phi(a',r)alpha = phi(a,r'alpha) : P[a,c]

To express this we need some kind of subobject construction.

Could be written as an equalizer of

    (forall a. R[a,b] -> P[a,c]) => (forall a,a'. A[a,a'] -> R[a',b] -> P[a,c])

so if we add equalizers/pullbacks we can define this internally.

## Tensors, Powers and (Co)-equalizers in Span

Let's see if the previous section can be carried out in Span.
I.e., does Span have tensors and powers?

Clearly it has tensors

    A <- R -> B <- Q -> C

can be composed by pullback

    A <- R x_B Q -> C

And the syntax is very accurate to the construction (R x_B Q)(a,c) = exists b. R(a,b) x Q(b,c)

What about cotensors? Since span is symmetric, the two are the same

A <- R -> B
A <- P -> C

B <- R ▹ P -> C

the formula is (R ▹ P)(b,c) = forall a. R(a,b) -> P(a,c)

# Function Extensionality

Haven't run into a need for any kind of funext yet, but there might be
an issue if we include a "mixed" Sigma type (or mixed Pi):

G | * |- S set
G | a:C;b:D |- R set
----
G | a:C;b:D |- Sigma_{x : S} R set
