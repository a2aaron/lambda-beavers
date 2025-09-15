
see https:ww.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf
and also https:ww.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture13.pdf

# Beta Reduction Algorithm

(Note: assuming call by name semantics)
Let's say we are beta reducing something like this (λu.λv.u x) (a b)
In normal notation, what we do here is t1 {t2 / x}, which looks like the following:
λu.λv.u x | initial term
λu.λv.u x | replace all instances of x by (a b)
λu.λv.u (a b)

Note that we do respect variable shadowing--we only replace the variable if it is free (ie: not
bound in the term). For example, in reducing (λy.(λx.x λx.z) x) a, we would get
λy.(λx.x λx.z) x | initial term
λy.(λx.x λx.z) a | replace all *free* instances of x with a
In λx.x λx.z, the x is bound and is not free so we do not replace it

The overall procedure therefore, would look something like this:
(λx. t1) t2 -> t1 {t2 / x}

Where {t / x} is the substitution function, which looks like:

Substituting a literal:
y {t / x} = t if y == x
            y otherwise
change literal y into term t if y is the literal being subtituted, otherwise leave it alone
ex: y {λx.x / y} = λx.x
ex: a {λx.x / b} = a

Substituting an application
(t1 t2) {t / x} = (t1 {t / x}  t2 {t / x})
this one is simple, just recurse into the function and argument

Substituting an abstraction
(λy.t1) {t / x} = λy.t1 {t / x} where y != x and y is not in fv(t)
(where fv(t) means "the set of free variables of t")
Those last two conditionals are important! The first means that we only
substitute a literal in t1 if that literally is not being captured by the lambda (in this case, y)

so for example, (λa.x (λx.x)) {y / x}
= (λa.y (λx.x))
We do not substitute for the inner x because it's been bound to that inner λx

The second means that we don't allow name collisions.
For example, what should the result of (λy.x) {y / x} be?
We can substitute x, it's not bound to the λy at all, but we probably don't want to
substitute y for x as a *name*--y is bound. What we want it to be is is for those Ys to be distinct
eg: we would rather write (λy1.x) {y2 / x} = λy1.y2
Fortunately, we can always rename variables so that this works out. That's what this second
condition is doing--it's just ensuring that when we substitute, the argument of the lambda is
not already a free variable in the substituted term
(in other words, all variables in the term are assumed to be free with respect to the lambda,
which makes sense! that term came from outside the lambda anyways, so there's no way any
of them are already bound)

Finally to actually do our beta-reduction, we just drop out the outermost lambda that we subtituted
into. For example, in (λy.(λx.x λx.z) x) a, we had computed this substitution
λy.(λx.x λx.z) x {y / a} = λy.(λx.x λx.z) a
so our final term would just be λy.(λx.x λx.z) a (we drop the outer λy along with the a)


## Beta Reduction for Debruijn Indicies 

Alright. Cool, how do we translate this to Debruijn indicies?

Recall that our notation is using 1-indexed values, so λx.x = λ 1, not λ 0
A free variable in this notation is any index whose value would take it "outside" the current
term. This basically means that if the value for some index is greater than the current
depth it's in, then it's a free variable

ex: λa.λx.a = λ λ 2. If we just look at that inner fragement, λx.a, and assume that a remains in
the outer context like before, then we get λx.a = λ 2. Notice how 2 is greater than it's current
depth (if it would bound it would need to be 1).

Without the context, we won't know which specific value that the unbound a would be indexed as
eg: we could also have λa.λb.λx.a = λ λ λ 3, and now suddently our λx.a fragment looks like λ 3,
so the context matters here a lot.

First let's tackle substitution. It'll be very similar to normal substitution, but with two caveats
1. we don't need to worry about the whole variable renaming thing in the lambda-branch! all the
variables are guarenteed to be "differently named"/unambigious to which lambda/outer context they
are bound to!

2. we DO need to worry about indicies changing as a result of values becoming more nested
Recall that the depth of a variable means it will have a different index. eg: we have,
λx.x λa.x λb.x λc.x = λ 1 λ 2 λ 3 λ 4
All of those Xes refer to the same variable, but get different indicies due to being more deeply
nested.

So that means for our substitution operation, it needs to look like this:

Substituting a literal:
N {t / M} = t if N == M
            N otherwise
(basically the same)

Substituting an abstraction:
(t1 t2) {t / M} = (t1 {t / M}  t2 {t / M})
(basically the same)

Substituting an abstraction
(λ t1) {t / M} = λ t1 {up_one(t) / M + 1}

For this one, when we recurse into t1, all of the variables we care about replacing
are going to be one higher now, and we need to also bump up every variable in our substited
term by one to compensate for the depth

Note that up_one only modifies free varaibles within it's argument. This means that it won't
modify anything whose index is equal to or lower than it's depth. See shift_cutoff for
implementation.

Finally, to complete the beta-reduction, we need to take the body of our substituted term
and extract it from the lambda--this will drop every index in the term down by one.

Hence, the final rule for beta reduction will look like:
(λ t1) t2 = down_one(t1 {up_one(t) / 1})


## Beta Reduction - Usage Changes
Some notes on how usage changes
First, defining usage: Usage is a property of abstractions. A given abstraction binds a particular
variable to itself, which I will call the bound variable.
The usage of an abstraction is the number of times the bound variable appears in the body of
the abstraction. The usage is a natural number and can be zero.
As an example, in λa.λb.b, there are two abstractions. The first one binds a (λa) and the second
one binds b (λb). For the first one, it's usage is zero because a does not appear in the body
of λa. For the second one, it's usage is one because b appears once in the body.
We can also talk about the usage of an abstraction in a given subterm.
Consider this: λa.(λb.a b) (λc.a a).
The usage of a in λb is one, while the usage of a in λc is two.
In addition, the usage of b in λc and the usage of c in λb are both zero.
(We might say that, in the first paragraph, we were talking about "the usage of a in λa"
or "the usage of b in λb")

There are two things we care about that may change during substitution:
- child abstractions in body (incl body itself)
- parent abstractions in parent (incl parent itself)
Notably, the usages for body and it's children do not change because we are substituting arg
into body. arg cannot possibly capture
aany variables in the body subtree, since arg isn't in said subtree. Therefore, none of the
body usages change.
The parent-chain can have it's usage change, but fortunately this is easy to compute.
Suppose we have parent abstraction λx
Let's say that the usage of the body is A
and the usage of x in the args is B
then, when redex evaluation is done, args will be substituted into the body A times
Each time it is, we will get another copy of args containing B uses of x
This results in A * B usages getting added
Then, when we drop out the original args subtree, we lose B uses of x
This results in a total change of A * B - B = (A - 1) * B uses of x.
This explains the behavior of
few different cases such as:
1. If the usage of args in the body is 0, then the usage of x will decrease by B
   because (0 - 1) * B = -B
2. If the usage of args in the body is 1, then the usage of x remains constant
   because (1 - 1) * B = 0 * B = 0
3. If the usage of x in args is 0, then the usage of x remains constant
   because (A - 1) * 0 = 0
(Moreover, if the (total) usage of x is 0, then after evaluation, the usage of x remains
zero.)