#import "lapreprint.typ": template
#import "@preview/lovelace:0.2.0": *
#import "@preview/showybox:2.0.1": showybox
#import "@preview/algo:0.3.3": algo, i, d, comment, code
#import "@preview/colorful-boxes:1.2.0": *
#import "@preview/fletcher:0.4.5" as fletcher: diagram, node, edge

#show: setup-lovelace

// #show figure.caption: it => [
//   #underline(it.body) |
//   #it.supplement
//   #context it.counter.display(it.numbering)
// ]

#let colred(x) = text(fill: red, $#x$)
#let colgray(x) = text(fill: gray, $#x$)

// Problem Callout Block
#let problem(title, content) = figure(
    showybox(
        frame: (
            border-color: red.darken(50%),
            title-color: red.lighten(60%),
            body-color: red.lighten(80%)
        ),
        title-style: (
            color: black,
            weight: "regular",
            align: center
        ),
        title: title,
        content
    ),
    supplement: [Problem],
    kind: "Problem",
)

// Theorem / Lemma Callout Block
#let theorem(content) = figure(
    showybox(
        frame: (
            border-color: purple.darken(40%),
            body-color: purple.lighten(95%)
        ),
        content
    ),
    supplement: [Theorem],
    kind: "Theorem",
)


// Definition Callout Block
#let definition(content) = figure(
    showybox(
        frame: (
            border-color: green.darken(40%),
            body-color: green.lighten(95%)
        ),
        content
    ),
    supplement: [Definition],
    kind: "Definition",
)

// Examples Callout Block
#let example(content) = figure(
    showybox(
        frame: (
            border-color: blue.darken(40%),
            body-color: blue.lighten(95%)
        ),
        content
    ),
    supplement: [Example],
    kind: "Example"
)

#let losing_definition(num, content) = colorbox(
    title: "Definition " + str(num),
    color: "green",
    radius: 4pt,
    width: auto,
    content
)

#show: template.with(
  title: "Model Repair and Conformance Checking of Time-Aware Models",
  theme: red.darken(50%),
  authors: (
      (
          name: "Shubh Sharma",
          affiliations: "1, 2",

      ),
      (
          name: "Thomas Chatain",
          affiliations: "2",
          orchid : "0000-0002-1470-5074",
      ),
  ),
    affiliations: (
   (id: "1", name: "Chennai Mathematical Institute"),
   (id: "2", name: "LSV, ENS Paris-Saclay"),
  ),
  abstract: (
      (
          title: "Abstract",
          content: "The subject of this paper is to implement model repair for timed models, that is, process models that consider both the sequence of events in a process as well as the timestamps at which each event is recorded. Time aware process mining is a growing subfield of researchh, and as tools that seek to discover timing related properties in the process develop, so does the need for conformance checking techniques that give insightful quality measure, for the purpose of this paper, we use alignments as witness for the model being unfit, we then give algorithms improving the models"),
  ),
    keywords: ("Time Petri Nets", "Model Repair", "Conformance Checking"),
    kind: "Research Internship",
    bibliography-file : "ref.bib"
)

= Introduction
== Process Mining and Model Repair
_Process Mining_ is a family of techniques used to analyze event data in order to understand and improve the system. It studies the system through their event logs and seeks to extract meaningful ways to model the underlying process to understand the system better or to predict it's future behaviour @Process-Mining.

The first step: _discovery_, in process mining is the discovery of a model one expects to model the system through techniques like machine learning. But the unexplainability of the approaches that ML takes naturally makes one questions if the produced model approximates the target system well enough. \
This is where _Conformance Checking_ comes in. Conformace Checking is a set of techniques used to comapre a _process model_ with an event log and rate it over some parameters like:
- Fitness : Does the model exhibit the beahviours specified in the logs?
- Precision : Does the model deviate a lot from the behavior specified in the logs?
- Generalization : Does the correctly predict behavior of the system outside the given logs?
- Simplicity : Is the model the simplest model that describes the log accurately?
Once we measure how well the model conforms to the given set of logs, we move to the next step that is _enahncement_: where and existing process model is extended or improved using information about the actual process record in some event log.

#set page(margin: auto)

Another important part of Process Mining is Performance Analysis where the goal is to analyze and improve the exectution of the model to use less time and resources an improve its performance data.

_Model Repair_ is a special case of *Enhancement* that deals with improving the model to more accurately fit any discrepancies due to events in the system that happen after the model has been constructed. The improvment metrics are usually one of the 4 mentioned above, this paper focuses on the fitness of the model.

== Time Aware Models
Process Models are represented by formal objects. Petri-Nets are offer a graphical means to represent concurrent systems and a formal semantics for their exectution. The setup is similar to the one in @Timed-Alignments where an event is represented by a letter from a finite alphabet (a set of possible discrete events). Logs is represented by the set of timed words over the alphabet, which is a list of events along with the timestamps on which the event occured. The notion of distance between words, which will give our conformance metric will be similar to the Levenstein's edit distance where we find the quickest way to go from one timed-word to another using a given set of edit actions.

We will be using Time Petri Nets, which are a variant of Petri Nets that can check the duration it takes to fire a transition once it's enabled, restricting the set of timed-words it accepts, this can be used to construct relationships and constraints between events and the timestamps at which they can be taken as seen in the logs.

= Preliminaries
== Time Petri Nets
We represent an event as pairs $(a, t)$ where $a in Sigma$ is the action and $t$ denotes the time at which the action was taken.

// #losing_definition(1, [ A _timed trace_ is a sequence $gamma in (Sigma times RR^+)^*$ of timed events, seen as a timed word. ])

#definition([ #text(weight: "bold", "Definition 1:") A _timed trace_ is a sequence $gamma in (Sigma times RR^+)^*$ of timed events, seen as a timed word. ]) <def1>

We will often ignore the untimed part of the word, i.e. project it on to the time component leaving a word in $(RR^+)^*$.

The Process Model we use here is a Time Petri Net.

#definition([
    *Definition 2:* A _Labelled Timed Petri Net_ (or $"TPN"$) is a tuple $cal(N) = angle.l P, T, F, "SI", Sigma, lambda, M_0, M_f angle.r$ where
    - $P$ and $T$ are disjoint sets of places and transitions respectively.
    - $F subset.eq (P times T) union (T times P)$ is the flow relation.
    - $"SI" : T -> II$ is the static interval function, $"SI"(t) = ("st"(t), "en"(t))$ where
        - $"st"(t)$ is the smallest valid time interval from the enabling of $t$ to its firing.
        - $"en"(t)$ is the largest valid time interval from the enabling of $t$ to its firing.
    - $lambda : T -> Sigma$ is a labelling function for the transition with actions from the action set $Sigma$
    - $M_0$ and $M_f : P -> NN$ are the initial and final markings.
]) <def2>


Given a transition $t in T$ we define
- The Pre-set of $t$ from as $""^circle.filled.small t = {p in P | (p, t) in F}$
- The Post-set as $t^circle.filled.small = { p in P | (t, p) in F }$ (we define pre-set and post-set if places similarly).
- We say that a transition $t$ is enabled at a marking $M$ if $forall p in ""^circle.filled.small t, M(p) > 0$
- The set of all enabled transitions in $M$ is given by $"Enabled"(M) = {t in T | t "is enabled in " M}$.

#definition([
    *Definition 3:* The _state_ (or _configuration_) of a $"TPN" cal(N) = angle.l P, T, F, "SI", Sigma, lambda, M_0, M_f angle.r$ is a pair $S = (M, I)$ where $M$ is a marking and $I : "Enabled"(M) -> RR^+$ is the clock function keeping track of the time since each transition was enabled. We set the inital state to be $(M_0, bold(0))$ where $bold(0)$ is the zero-function.
]) <def3>

A transition $t$ is said to be *fireable* after a delay $theta$ from a state $S=(M, I)$ if $t$ is enabled in $M$ and $I(t) + theta in "SI"(t)$

The update to the marking and time function are defined below:
#definition([
    *Definition 4:* (_Firing Rule_) When a transition $t$ fires after a delay $theta$ from state $S = (M, I)$, the new state $S' = (M', I')$ is given as follows:
    #math.equation(block: true, numbering: none)[
    $M' = (M without ""^circle.filled.small t) union t^circle.filled.small\
     I'(t) = cases(
     I(t) + theta quad quad & "If" t in "Enabled"(M'),
     0 & "If" t in "Enabled"(M') "and" t in.not "Enabled"(M),
     "Undefined" & "Otherwise",)$]
    This is also denoted as $S [t angle.r S'$
]) <def4>

A valid execution of the model starts at the initial marking $M_0$, fires a sequence of transitions and ends at the final marking $M_f$.

#example([
    *Example 1:* Consider the following example of a Time Petri Net $N$: \
#figure(
    diagram(
        spacing: (25pt, 20pt),
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <p1>),
        node((2,-1), stroke: 0.5pt, radius: 2mm, name: <p2>),
        node((2,1), stroke: 0.5pt, radius: 2mm, name: <p3>),
        node((4,-1), stroke: 0.5pt, radius: 2mm, name: <p4>),
        node((4,1), stroke: 0.5pt, radius: 2mm, name: <p5>),
        node((6,0), stroke: 0.5pt, radius: 2mm, name: <p6>),
        node((1, 0), $a$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t1>),
        node((3, -1), $b$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t2>),
        node((3, 0), $c$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t3>),
        node((1, 1), $d$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t4>),
        node((3, 1), $e$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t5>),
        node((5, 0), $f$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t6>),
        edge(<p1>, <t1>, "-|>"),
        edge(<p2>, <t2>, "-|>"),
        edge(<p2>, <t3>, "-|>", bend: -20deg),
        edge(<p3>, <t4>, "-|>"),
        edge(<p3>, <t5>, "-|>"),
        edge(<p4>, <t6>, "-|>", bend: 20deg),
        edge(<p5>, <t6>, "-|>", bend: -20deg),
        edge(<t1>, <p2>, "-|>", bend: 20deg),
        edge(<t1>, <p3>, "-|>", bend: -20deg),
        edge(<t2>, <p4>, "-|>"),
        edge(<t3>, <p4>, "-|>", bend: -20deg),
        edge(<t4>, <p3>, "-|>", bend: -40deg),
        edge(<t5>, <p5>, "-|>"),
        edge(<t6>, <p6>, "-|>"),
        node((0.8, -0.4), text(size: 7pt, $[0, oo)$)),
        node((3, -1.4), text(size: 7pt, $[1, 1]$)),
        node((3, 0.35), text(size: 7pt, $[0, 2]$)),
        node((0.65, 1), text(size: 7pt, $[1, 3]$)),
        node((3, 1.4), text(size: 7pt, $[1, 4]$)),
        node((5.3, -0.4), text(size: 7pt, $[0, 3]$)),
    )) \
    One possible execution of $N$ would be for the firing sequence
    #math.equation(block: true, numbering: none)[
        $w = (a, 1)(b, 2)(d, 3)(e, 4)(f, 5)$
    ]
    The initial marking only has $a$ enabled and firing $a$ moves the token to places that enable $b,c,d$ and $e$. Then transition $b$ at time $2$ is fired, which puts a token in one of the places consumed by transition $f$. at time $3$, $d$ is fired followed by $e$ at $4$ and now $f$ is enabled and is fired after a second of wait.
]) <ex1>


Now we can define the langauge of the Time Petri Net as follows
#definition([
    *Definition 5:* A word $w= a_0 a_1 ... a_n in Sigma^*$ is in the _language of the Labelled Time Petri Net_ $cal(L(N))$ if there is a fireable sequence of transitions $(t_0, t_1 ... t_n)$ such that $lambda(t_0, t_1 ... t_n) = w$ and if the sequence of transitions is taken from the initial state $M_0$, it will end at the final transition $M_f$.
    #math.equation(block: true, numbering: none)[
        $(M_0, bold(0)) [t_0 t_1 ... t_n angle.r (M_f, I)$
    ]
]) <def5>


== Helper Definitions
To help with defining some of the things that will be used further
, we will use *causal nets* which are like unfoldings of a Petri Net that will make definitions and procedures about walking though the Petri Net easier.

#definition([
    *Definition 6:* A _Causal Net_ $"CN":= angle.l B, E, G angle.r$ is a finitary, acyclic net where
    #math.equation(block: true, numbering: none)[
        $forall b in B: |b^circle.filled.small | <= 1 and |""^circle.filled.small b| <= 1$
    ]
]) <def6>

This definition reads as "A Petri net where each place has at most 1 in-transition and at most 1 out-transition". We can also think of this as taking the original petri net and everytime we see a state with multiple out-transitions we copy the state and the net constructed till now once for each transition, we do the same for out-transitions.

Once we construct a Causal Net for a Petri Net we need to connect the execution of the Causal Net with that of the Petri Net. This will be done using a homomorphism.

#definition([
    *Definition 7:* A mapping $p: B union E -> P union T$ is a _homomorphism_ if:
    - $forall e in E, p(e^circle.filled.small) = p(e)^circle.filled.small$
    - $forall e in E, p(""^circle.filled.small e) = ""^circle.filled.small p(e)$
    - $M_(0("causal net")) = p(M_(0("Petri net")))$
]) <def7>

We will use a Causal Net and a homomorphism together as

#definition([
    *Definition 8:* A _Causal Process_ of a Time Petri Net $cal(N)$ is a pair $("CN", p)$ wher $"CN"$ is a causal net and $p$ is a homomorphism from $"CN"$ to $cal(N)$.
]) <def8>

Using $p$, the elements of $"CN"$ are identified with their corresponding elements in $cal(N)$. As a result, any run in the Causal Process corresponds uniquely to an untimed run in a Timed Petri Net. To also associate time stamps with our Causal Process we define

#definition([
    *Definition 9:* A _Timing Function_ $tau: E -> RR^+$ is a function from events of a causal process into time values.
]) <def9>

== Conformance Metric
Conformance Checking tries to measure how well a process model mimics the system, some of the metrices used for that are defined below.

#definition([
    *Definition 10:* Given a process model $cal(N)$ and a log $L$ we define the _fitness_ of $cal(N)$ with respect to $L$ as
    #math.equation(block:true, numbering : none)[
        $"fitness"(cal(N), L) = 1 - max_(sigma in L) "dist"^*(sigma, cal(L(N)))$
    ]
]) <def10>

Here $"dist"^*$ is some normalized distance between traces, some options are defined later.

The fitness of the model is high if all of the observed behaviors in the logs are closely captured by the model.

#definition([
    *Definition 11:* Given a process model $cal(N)$ and a log $L$ we define the _precision_ of $cal(N)$ with respect to $L$ as
    #math.equation(block:true, numbering : none)[
        $"precision"(cal(N), L) = 1 - max_(w in cal(L(N))) "dist"^*(L, w)$
    ]
]) <def11>

We have that the precision of the model is high if it does not exhibit behavior that deviates too much from the observed logs.

= Conformance Checking and Model Repair in Timed Setting
The Problem of Model Repair is, given an event log, a process model and some budget, compute the edits that can be made to the model under the budget to improve the conformance of the model to the system by some metric. If we let a Time Petri Net be our process model and fitness me our conformance metric then the problem can be stated as :

#problem("Model Repair of Time Petri Net (General)")[Given a process $cal(N)$ denoted by a Time Petri Net, a log $L$ and a budget $beta$, we wish to find an edit of the $cal(N) -> cal(N')$ that can be implemented under the given budget constraint and optimally increases the fitness.] <prob1>

The two ways in which the model can be imperfect fitness is to have traces in the log such that
- $"Untime"(L) subset.not.eq "Untime"(cal(L)(cal(N)))$, i.e there are traces where the sequence of events is not captured by $cal(N)$
- There exists a trace whose untimed version is in the langauge, but the timestamps do not match with any word in the language of $cal(N)$

#example[
    *Example 2:* Consider the Process Model in @ex1 and consider the the following observed traces.
    - $sigma_1 = (a, 0)(a, 1)(b, 2)(d, 3),(e, 3)(f, 5)$
        - Clearly, there is no trace in the process model that has more than 1 $a$, which means the structure of the model itself needs to be updated by adding/removing states and transitions.
    - $sigma_2 = (a, 1)(b, 1)(d, 3)(e, 4)(f, 5)$
        - The sequence of transitions in $sigma_2$ can happen in the model but for transition $b$ we need to wait for at least $1$ unit. Changing the timestamp for that transition to $2$ gives a trace that has a run in the petri net.
    - $sigma_3 = (a, 1)(d, 1)(d, 2)(e, 4)(f, 5)$
        - This trace is also not possbile in the model as transition $b$ or $c$ must be fired to enable transition $f$. This can be fixed by relabelling transition $b$ or $c$.
] <ex2>

In the untimed setting, this problems is veiwed as minimzing cost over a series of edit moves which are either insertions or deletions to the model. For the timed case there are two aspects that need to be improved, which are mentioned above. This problem has been studied for the untimed case, but the timed settings is more complex.

Also, in practice, a large set of malfuctionings can be modeled as temporal anomalies (a slowing down of a conveyor belt speed due to wear, a shorter duration of a work phase due to to an incorrect handling of the operator, a causal change in a timer duration, etc.) and the problem is a pre-requisite for the general case of dealing with all kinds of errors. In this paper we will be focusing on the purely timed version of the model repair problem. i.e where the only anomalies that are fixed are temporal ones (All traces that are not in the language of the model will have an issue similar to $sigma_2$ in @ex2)

#problem("Model Repair of Time Petri Nets (Purely Timed)")[Given a process $cal(N)$ denoted by a Time Petri Net, a log $L$ and a budget $beta$, we wish to find an edit of the $cal(N) -> cal(N')$ that can be implemented under the given budget constraint and optimally increases the fitness. We also have the constraint that $forall sigma in L, "Untime"(sigma)$ gives a valid causal process for $cal(N)$.] <prob2>

To properly formalize the problem we need definitions for editing out petri net and conformance for which we need to define out distance functions.

== Edits and Distances
Out notion of distance is similar to that of Levenstein's edit distance where we are given a set of edit actions and we try to go from one trace to another in the shortest way, representing in some sense how different 2 traces are, there are 2 options that are considered usually

#definition([
    *Definition 12:* (_Stamp Edit_) Given a timing function $gamma : E -> RR^+$, we define the a stamp move as:
    #math.equation(block: true, numbering: none)[
        $
            forall x in RR, e in E : "stamp"(x, e)(gamma) = gamma' "where"\
            forall e' in E : gamma'(e) = cases(
            gamma (e') + x quad & e' = e,
            gamma (e')& "otherwise"
            )
        $
    ]
]) <def12>

i.e we edit the timestamp at which a particular transition ($e$) was taken by $x$. These edits only affect a single transition, and can represent a reading error in the model which needs to corrected without affecting the other timestamps.


Another natural edit move the consider is :
#definition([
    *Definition 13:* (_Delay Edit_) Given a timing function $gamma : E -> RR^+$, we define the a delay move as:
    #math.equation(block: true, numbering: none)[
        $
            forall x in RR, e in E : "stamp"(x, e)(gamma) = gamma' "where"\
            forall e' in E : gamma'(e) = cases(
            gamma (e') + x quad & e' >= ""_G e,
            gamma (e')& "otherwise"
            )
        $
    ]
])

Here the relation $>= ""_G$ can be thought of as a causal one, i.e if $e$ must happen for $e'$ to happen then $e <= ""_G e'$.

Intuitively, this edit represents a change in the duration one waits before taking a transition, this is why timestamps of all subsequent transitions are also changed by the same amount.

Using these 2 distance we can define out notion of distance. We assign a cost to each edit move say for both delay and stamp edits we say that the cost of an edit is the same as the change $x$, using that we can define the following 3 definitions:

#figure(
showybox(
    frame: (
        border-color: green.darken(40%),
        body-color: green.lighten(95%)
    ),
    [
        *Definition 14:* (_Stamp Only Distance $d_t$_) Given any two timing functions $tau_1, tau_2$ over the same causal process $("CN", p)$, we define the stamp distance as
        #math.equation(block : true, numbering: none)[$
            d_t(tau_1, tau_2) = min {"cost"(m) | m in "Stamp"^*, m(tau_1) = tau_2}
        $]
    ],
    [
        *Definition 15:* (_Delay Only Distance $d_theta$_) Given any two timing functions $tau_1, tau_2$ over the same causal process $("CN", p)$, we define the stamp distance as
        #math.equation(block : true, numbering: none)[$
            d_theta(tau_1, tau_2) = min {"cost"(m) | m in "Delay"^*, m(tau_1) = tau_2}
        $]
    ],
    [
        *Definition 16:* (_Mixed Moves Distance $d_N$_) Given any two timing functions $tau_1, tau_2$ over the same causal process $("CN", p)$, we define the stamp distance as
        #math.equation(block : true, numbering: none)[$
            d_N(tau_1, tau_2) = min {"cost"(m) | m in ("Stamp" union "Delay")^*, m(tau_1) = tau_2}
        $]
    ],
),
    kind: "Definition",
    supplement: [Definition]
) <def14-16>

= Results
== Sequential Petri Nets and Delay-Only Distance <restrictions>
We first focus out attention to a restricted version of problem where:

- The model in question will be a *Sequential Time Petri Net*, which means that, there is a dedicated start state and a dedicated end state, and each transition, connects one state, to one other state in a way that the underlying graph looks like a line graph, which the start and end states acting as the two ends of the graph.
- The problem is restricited to a *Purely Timed Problem*, which means that the sequence of transitions represent the sequence of events in the system correctly, but the timestamps might not be accurate.
- The metric for measure which will be used is going to be *Delay-Only Distance* #link(<def14-16>)[(Definition 15)]
- For the edits to the mode, we cost $x$ unit of the budget whenever any bound of a time range of a transition is changed by $x$.
- The conformance metric used is _fitness_ but here we define it as $- (max_(sigma in L) "dist"_theta (sigma, cal(L(N)))$ which can be easily converted to the normalized distance used in the original definition.
- Another thing to note is that a Sequential Petri Net is isomorphic to it's Causal Net, hence we will not make a distinction between the two here.

#example[
    *Example 3:* We start with a simple example and informally go over the procedure

    Consider the following Time Petri Net $N$
    #figure(
    diagram(
        spacing: (25pt, 20pt),
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <p1>),
        node((2,0), stroke: 0.5pt, radius: 2mm, name: <p2>),
        node((4,0), stroke: 0.5pt, radius: 2mm, name: <p3>),
        node((6,0), stroke: 0.5pt, radius: 2mm, name: <p4>),
        node((1, 0), $a$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t1>),
        node((3, 0), $b$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t2>),
        node((5, 0), $c$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t3>),
        edge(<p1>, <t1>, "-|>"),
        edge(<t1>, <p2>, "-|>"),
        edge(<p2>, <t2>, "-|>"),
        edge(<t2>, <p3>, "-|>"),
        edge(<p3>, <t3>, "-|>"),
        edge(<t3>, <p4>, "-|>"),
        node((1, -0.4), text(size: 7pt, $[1, 2]$)),
        node((3, -0.4), text(size: 7pt, $[1, 3]$)),
        node((5, -0.4), text(size: 7pt, $[0, 2]$)),
        node((0, -0.4), text(size: 7pt, "i")),
        node((2, -0.4), text(size: 7pt, "ii")),
        node((4, -0.4), text(size: 7pt, "iii")),
        node((6, -0.4), text(size: 7pt, "iv")),
    ))
] <ex3>
// Can't figure out how to get a page break so 2 blocks :p

#example[

    We are also given the following log
    #math.equation(block:true, numbering:none)[$
        L =  mat(delim:"{",
        "[" (a, 1), (b, 5), (c, 9)"]," ;
        "[" (a, 0), (b, 5), (c, 7)"]" ;
        )
    $]

    And we are given the budget $beta = 2$.

    Our goal is to edit the model by making a change of at most $beta = 2$ to the boundaries of the transitions in order to minimize the distance of the logs from the model. The Procedure will go as follows:

    - The transitions only keep track of the delay that is done to trigger them, so it will be easier to look at traces with wait times before the previous transitions rather than the next one, so we construct the following
    #math.equation(block:true, numbering:none)[$
        F =  mat(delim:"{",
        "[" (a, 1), (b, 4), (c, 4)"]," ;
        "[" (a, 0), (b, 5), (c, 2)"]" ;
        )
    $]

    And now it is easier to see that neither of the traces have a corresponding run in $N$, also, the distance of each transition is now easy to compute, for both the transitions it's $3$. So the fitness is $-3$ and we need to reduce the distance of the model from each of the traces to improve the fitness of $N$.

    Trace 1 takes transition $b$ and $c$ too late, where as Trace $2$ takes transition $b$ late and takes transition $a$ too early. This means that increasing the upper bound of transition $b$ reduce the distance of both traces, and hence will be optimal, so we spend our budget on $b$.

    After spending 1 unit of budget though the model changes to
    #figure(
    diagram(
        spacing: (25pt, 20pt),
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <p1>),
        node((2,0), stroke: 0.5pt, radius: 2mm, name: <p2>),
        node((4,0), stroke: 0.5pt, radius: 2mm, name: <p3>),
        node((6,0), stroke: 0.5pt, radius: 2mm, name: <p4>),
        node((1, 0), $a$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t1>),
        node((3, 0), $b$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t2>),
        node((5, 0), $c$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t3>),
        edge(<p1>, <t1>, "-|>"),
        edge(<t1>, <p2>, "-|>"),
        edge(<p2>, <t2>, "-|>"),
        edge(<t2>, <p3>, "-|>"),
        edge(<p3>, <t3>, "-|>"),
        edge(<t3>, <p4>, "-|>"),
        node((1, -0.4), text(size: 7pt, $[1, 2]$)),
        node((3, -0.4), text(size: 7pt, $[1, colred(4)]$)),
        node((3, -0.65), text(size: 7pt, $colgray([1, 3])$)),
        node((5, -0.4), text(size: 7pt, $[0, 2]$)),
        node((0, -0.4), text(size: 7pt, "i")),
        node((2, -0.4), text(size: 7pt, "ii")),
        node((4, -0.4), text(size: 7pt, "iii")),
        node((6, -0.4), text(size: 7pt, "iv")),
    ))

    And now trace 1 takes the transition $b$ at the correct time. If we continue to spend out budget entirely on $b$ then we will not reduce the distance of trace 1 from the model anymore and hence will not change the fitness of the model.

    So we need to rethink our distribution of the budget. We need to reduce the distance of both the traces from the model, hence we need to spend budget in a way that improves fitness. One way to do it optimally would be to split our leftover budget evenly between transition $b$ and $c$. And finally ending with the following model.

    #figure(
    diagram(
        spacing: (25pt, 20pt),
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <p1>),
        node((2,0), stroke: 0.5pt, radius: 2mm, name: <p2>),
        node((4,0), stroke: 0.5pt, radius: 2mm, name: <p3>),
        node((6,0), stroke: 0.5pt, radius: 2mm, name: <p4>),
        node((1, 0), $a$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t1>),
        node((3, 0), $b$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t2>),
        node((5, 0), $c$, stroke: 0.5pt, shape: rect, width: 4mm, height: 5mm, name: <t3>),
        edge(<p1>, <t1>, "-|>"),
        edge(<t1>, <p2>, "-|>"),
        edge(<p2>, <t2>, "-|>"),
        edge(<t2>, <p3>, "-|>"),
        edge(<p3>, <t3>, "-|>"),
        edge(<t3>, <p4>, "-|>"),
        node((1, -0.4), text(size: 7pt, $[1, 2]$)),
        node((3, -0.4), text(size: 7pt, $[1, colred(4.5)]$)),
        node((3, -0.65), text(size: 7pt, $colgray([1, 4])$)),
        node((5, -0.4), text(size: 7pt, $[0, colred(2.5)]$)),
        node((5, -0.65), text(size: 7pt, $colgray([0, 2])$)),
        node((0, -0.4), text(size: 7pt, "i")),
        node((2, -0.4), text(size: 7pt, "ii")),
        node((4, -0.4), text(size: 7pt, "iii")),
        node((6, -0.4), text(size: 7pt, "iv")),
    ))

    Now we can stop as we have consumed all our budget and the distance of each trace from the model is $1.5$.

    Note that this is not the only optimal solution, reducing the lower bound of transition $a$ instead of increasing the upper bound $b$ in step to also leads to the same improvement in fitness.
]

#pagebreak()

=== Reduction to simpler cases

Note that the only 2 kinds of edits one would want to make to the petri net are:
- increasing the upper bound of a transition
- decreasing a lower bound of a transition
This is because these are precisely the edits that would increase the size of the language of the petri net, and other edits make the language of the petri-net strictly smaller.

We now try to reduce the petri-net in a way that we would only have to deal with 1 type of edit.

We restrict the input set of petri nets to those which in which the static interval function is the constant function $x |-> [0,0]$.

Given a Sequential Time Petri-net $cal(N)$ and a trace $tau$ on it we can reduce it to a Sequential Time Petri-net $cal(N')$ with the above definition in the following:
- If the original set of transitions was $T$ then let $T' = {t_"start" | t in T} union {t_"end" | t in T}$
- Given places $p_i$ and $p_(i+1)$ and a transition $t_i$ such that $""^circle.filled.small t_i = {p_i}$ and $t_i^circle.filled.small = {p_(i+1)}$ we make states $q_i, q'_i, q_(i+1)$ such that
    - $""^circle.filled.small text(t_i)_"start" = {q_i}$
    - $text(t_i)_"start"^circle.filled.small = {q'_i}$
    - $""^circle.filled.small text(t_i)_"end" = {q'_i}$
    - $text(t_i)_"end"^circle.filled.small = {q_(i+1)}$

This procedure takes in each transition and copies it, one copy for the start boundry of the transition, and one for the end.

Given a flow function $f$ for $cal(N)$, we can define $f'$ for $cal(N')$ as follows:
- If $f = f_1 f_2 ... f_n$ we let $f' = text(f'_1)_"start" text(f'_1)_"end" space text(f'_2)_"start" ... text(f'_n)_"end"$,  note that $|f'| = 2 |f|$.
- If $t_i = angle.l "st"_i, "en"_i angle.r$ then
    - If $f_i < "st"_i$ we let $text(f'_i)_"start" = "st"_i - f_i$ and $text(f'_i)_"end" = 0$
    - If $f_i > "en"_i$ we let $text(f'_i)_"start" = 0$ and $text(f'_i)_"end" = f_i - "en"_i$
    - otherwise we let $text(f'_i)_"start" = text(f'_i)_"end" = 0$


#example([
    *Example 4:* Consider the Petri Net $N$ and the flow functions $F$ on them.\
    Using the above construction we get the following $N'$

    #figure(
    diagram(
        spacing: (25pt, 20pt),
        // Places
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <q1>),
        node((1,0), stroke: 0.5pt, radius: 2mm, name: <p1>),
        node((2,0), stroke: 0.5pt, radius: 2mm, name: <q2>),
        node((3,0), stroke: 0.5pt, radius: 2mm, name: <p2>),
        node((4,0), stroke: 0.5pt, radius: 2mm, name: <q3>),
        node((5,0), stroke: 0.5pt, radius: 2mm, name: <p3>),
        node((6,0), stroke: 0.5pt, radius: 2mm, name: <q4>),
        node((0, -0.4), text(size: 7pt, $q_1$)),
        node((2, -0.4), text(size: 7pt, $q_2$)),
        node((4, -0.4), text(size: 7pt, $q_3$)),
        node((6, -0.4), text(size: 7pt, $q_4$)),
        node((1, -0.4), text(size: 7pt, $q'_1$)),
        node((3, -0.4), text(size: 7pt, $q'_2$)),
        node((5, -0.4), text(size: 7pt, $q'_3$)),

        // Transitions
        node((0.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t1>),
        node((1.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t2>),
        node((2.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t3>),
        node((3.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t4>),
        node((4.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t5>),
        node((5.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t6>),
        node((0.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((1.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((2.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((3.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((4.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((5.5, 0.4), text(size: 5pt, $[0, 0]$)),

        // Arcs
        edge(<q1>, <t1>, "|->"),
        edge(<t1>, <p1>, "|->"),
        edge(<p1>, <t2>, "|->"),
        edge(<t2>, <q2>, "|->"),
        edge(<q2>, <t3>, "|->"),
        edge(<t3>, <p2>, "|->"),
        edge(<p2>, <t4>, "|->"),
        edge(<t4>, <q3>, "|->"),
        edge(<q3>, <t5>, "|->"),
        edge(<t5>, <p3>, "|->"),
        edge(<p3>, <t6>, "|->"),
        edge(<t6>, <q4>, "|->"),
    ))

    And we can rewrite the set of flow functions as
    #math.equation(block:true, numbering:none)[$
        F =  mat(delim:"{",
        "[" 0, 0, 0, 1, 0, 2"]," ;
        "[" 1, 0, 0, 2, 0, 0"]" ;
        )
    $]

    Note: I am omitting the labelling of the transitions as they are not relevant here.
])

This conversion intuitively changes the petri net so that one can treat different boundaries of transitions as different transitions, taking a transition too early or too late will translate to taking the first transition too late or taking the second transition too late, which matches our goal of having just 1 kind of edit.

#theorem([
    *Theorem 1:* Given a Petri Net $cal(N)$ and a log $cal(L)$ and it's corresponding net and log in the restricted case $cal(N')$ and $cal(L')$, for each edit of cost $c$ that takes creates $cal(M)$ from $cal(N)$, there is an edit of cost $c$ that creates $cal(M')$ from $cal(N')$ such that
    - $cal(M')$ is the restricited version of $cal(M)$ which can also be constructed using the methods defined above
    - For any net $N$ and log $L$, it's restricted version $N'$ with $L'$ has the same fitness as $N$
    Hence solving model repair for this restricited class, solves it for general sequential petri nets too.
]) <theorem1>

Note: This can be made more efficient by only considering transitions for boundaries that matter. i.e, for an upper bound if a transition is taken too late in a trace, or for a lower bound if a transition is taken too early in a trace. This is especially easy to notice in petri-nets produced by editing the above restricited nets, apart from the first reduction, all other reductions either decrease the number of states or keep it the same.

This reduction will be assumed for @unfit, @gradient and @solving.

=== The $"unfit"$ function <unfit>

Given an a petri net $cal(N)$ with $n$ transitions, any edit, must increase the upper bound of a transition by some amount, so we can represent an edit by an $n$ dimesional vector, precisely the amount by which each upperbound of a transition is increased, formally, for any edit that takes a petri net $cal(N)$ to a petri net $cal(N')$, one can represent it as the vector $v$ such that $v(i) = cal(N')(i)_"end" - cal(N)(i)_"end"$. Where $cal(N)(i)_"end"$ is the upper bound of the static interval of the $i^"th"$ transition of net $cal(N)$.

Now the space $(RR^+)^n$ can be mapped to the space of the petri nets that can be creating by editing a given starting petri net $cal(N)$.

This lets us define the $"unfit" : (RR^+)^n -> RR$ function. The input of the function is a vector, which represents an edit to the original petri net $cal(N)$ and the output of the function is the negation of the fitness of the net obtained after the edit.

The following helper function $d' : RR times RR -> RR$ will be useful: $d'(a, b) = max(0, b-a)$

First we define the $"unfit"$ function for the case where there is just 1 trace in the log. Let the trace be $tau$ and it's flow function be $f$. Here the $"unfit"$ function is the same as the distance function.

For each transition $t_i$ of the petri net, we define $d_i (arrow(a), arrow(b)) = d'(arrow(a)(i), arrow(b)(i))$. Where $arrow(a)(i)$ is the $i^"th"$ component of $arrow(a)$.

Now that we have defined it for each component we let $D (arrow(a), arrow(b))= sum_(i = 1)^n d_i( arrow(a), arrow(b))$

#theorem([
    *Theorem 2:* Given a vector $arrow(a)$ representing an edit on the petri net $cal(N)$ producing $cal(N')$ and a flow function $f$ in $cal(F')$, $D(a, f)$ is precisely  $"dist"_theta$ between the edited net and $f$.
]) <theorem2>

#definition([
    *Definition 17:* Given a net $cal(N)$ with constant $[0,0]$ static interval functions for all transitions and a log $cal(L)$, the $"unfit"$ _function_ can be defined as follows.

    $
        "unfit"_cal((N, L))(a) = max_(f in cal(F')) D(a, f)
    $

]) <def17>

#theorem([
    *Corollary 3:* $"unfit"_cal((N, L))(a)$ is negation of the fitness of $cal(N)$ with respect to $cal(L)$.
]) <theorem3>

#example([
    *Example 5:* Consider the following net $cal(N)$ with 2 transitions

    #figure(
    diagram(
        spacing: (25pt, 20pt),
        // Places
        node((0,0), $circle.filled.small$, stroke: 0.5pt, radius: 2mm, name: <q1>),
        node((1,0), stroke: 0.5pt, radius: 2mm, name: <q2>),
        node((2,0), stroke: 0.5pt, radius: 2mm, name: <q3>),
        node((0, -0.4), text(size: 7pt, $q_1$)),
        node((1, -0.4), text(size: 7pt, $q_2$)),
        node((2, -0.4), text(size: 7pt, $q_3$)),

        // Transitions
        node((0.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t1>),
        node((1.5, 0), stroke: 0.5pt, shape: rect, width: 0.5mm, height: 5mm, name: <t2>),
        node((0.5, 0.4), text(size: 5pt, $[0, 0]$)),
        node((1.5, 0.4), text(size: 5pt, $[0, 0]$)),

        // Arcs
        edge(<q1>, <t1>, "|->"),
        edge(<t1>, <q2>, "|->"),
        edge(<q2>, <t2>, "|->"),
        edge(<t2>, <q3>, "|->"),
    ))

    And the following set of flow functions for it
    #math.equation(block:true, numbering:none)[$
        F =  mat(delim:"{",
        f_1, =, "[" 2, 0"]," ;
        f_2, =, "[" 0, 2"]," ;
        f_3, =, "[" 1.5, 1.5"]," ;
        )
    $]

    And the following are the graphs of the $"unfit"$ functions

    #grid(
        columns: (auto, auto, auto),
        figure(
            image("Images/unfit_ex_f1.png", width: 80%),
            caption: [
                $"unfit"$ function for $f_1$
            ],
            kind: "Image",
            supplement: [Image]

        ),
        figure(
            image("Images/unfit_ex_f2.png", width: 80%),
            caption: [
                $"unfit"$ function for $f_2$
            ],
            kind: "Image",
            supplement: [Image]

        ),
        figure(
            image("Images/unfit_ex_f3.png", width: 80%),
            caption: [
                $"unfit"$ function for $f_3$
            ],
            kind: "Image",
            supplement: [Image]

        ),
    )

    #figure(
        image("Images/unfit_ex_final.png", width: 30%),
        caption: [
            $"unfit"$ function for the entire problem
        ],
        kind: "Image",
        supplement: [Image]

    )

]) <ex5>

=== Gradient Descent <gradient>

#theorem([
    *Theorem 4:* Some properties of the $"unfit"$ functions:

    The $"unfit"$ functions turns out to have a ton of nice properties.
    - The function $d_i$ is continuous and a piecewise function, linear in each part.
    - It is also a convex function.
    - Since $"unfit"$ us just multiple $d_i$ functions combined using $max$ and summation. which means it's also continuous, piecewise linear, and a convex function.
    - Also the domain of the function in general is $(R^+)^n$, but it can be restricted to all vectors such that the sum of their components ($p_1$ norm) $<= beta$ to give the problem a budget. In their scenarios the input space is a convex set.
])

These properties make it really good for gradient descent. Hence we will choose that as our strategy to solve the problem, it also precisely matches an intuitive direct startegy of finding the way to distribute the budgets to make changes optimal locally.

Gradient Descent is a greedy mathematical optimization techniques that involves starting at a point in the input space and moving in the opposite direction of the gradient(in the direction where the function decreases at the highest rate), until a local minimum is reached.

For our case picking Gradient Descent is a good option because:
- The function is piecewise linear, which means each part the gradient is constant and can be computed easily using linear programming.
- The function is convex with a convex set as it's input space, which means that there is only 1 set of global minima which is also convex and no other critical point.
- The input space can be bounded. If the fitness of the model is $-k$ then the we can bound the input space to all vectors whose $p_1$ norm is less than $k*|L|$. This is also a closed set, hence compact, which means the points that evaluate the global minima are in the set.

Therefore we can give the following algorithm for computing the model repair problem
- We start at the point $bold(0)$
- At every step we find the direction of steepest descent and we keep moving in that direction:
    - Consume the entire budget
    - A new trace becomes a trace with maximum distance from the net
    - Some trace with maximum distance from net has a transition which is taken at a time delay accepted by the edited petri net.
- Whenever we reach such a point, we do recompute the gradient and keep repeating this and the previous step.
- We stop when the bugdet runs out or when the model becomes fit.

=== Computing the Solution <solving>

We have defined our unfit function as the maximum of the distances of the log traces from the model. Let $cal(F)_"max"$ be the set of flow functions with maximum distance from $cal(N)$.

We now use linear programming to both compute the direction of steepest descent and the amount of budget to be spent in it before a recomputation is required.

We will be using the following list of variables.
- For every $t$ in the set of transitions of the petri net (denoted by $T$), we have a variable $b_t$ holding the budget assigned to $t$.
- For every $f$ in $cal(F)$ we have $"imp"_f$ denoting the reduction in distance of $f$ from $cal(N)$ because of the edit.
- $"improvement"$, holding the total change in the fitness of the model, hence our goal will be to maximize this.
- $"spend"$, holding the total amount of budget spent.

The following constants will be helpful in writing the equations
- We let $arrow(a) = bold(0)$
- $beta$, which is the total budget available
- $"un-fitness" = "unfit"_cal((N, L))(arrow(a))$
- For each $f in cal(F)$ we have $d_f = D(arrow(a), f)$, that is the distance of $f$ from $cal(N)$
- for each $f in cal(F)$, we let $d_(f, i) = f_i$
- For each $f in cal(F)$ and $t$ in $T$ we have $"affects"_(t, f)$ which is
    - $0$ if $t$ is the $i^"th"$ transitions and $d_i (arrow(a), f)=0$
    - $1$ otherwise

The goal of linear program is
$
    "Maximize"("improvement")
$

Under the constraints:
- We do not spend more than the total budget:
    $
        "spend" <= beta
    $
- Improvement in a flow function is the total budget assigned to the transitions which affect it, for each $f in cal(F)$ we have
    $
        "imp"_f = sum_(t in T) b_t times "affects"_(t, f)
    $
- Total improvement is the least improvement of all of the flow functions in $cal(F)_"max"$, so for each $f in cal(F)_"max"$
    $
        "improvement" <= "imp"_f
    $
- Computing the total amount of budget spent
    $
        "spend" = sum_(t in T) b_t
    $

The variables $b_t$ can be used to compute the direction of steepest descent, but we also add the following constrainst to calculate the largest "step size" after which we need to do recomputation.

- We need to recompute when a new flow function needs to be added to $cal(F)_max$ so for all $f in cal(F)$
    $
        "un-fitness" - "improvement" >= d_f - "imp"_f
    $
- We need to recompute each time the $"effects"$ variables become outdated, so for all $i in [1 ... n]$ let $t_i$ be the $i^"th"$ transition and forall $f in cal(F)$ we have
    $
        b_(t_i) <= d_(f, i)
    $

Once we get values of $b_(t_i)$ after solving the linear program, we get $arrow(a)(i) = b_(t_i)$ where $t_i$ is the $i^"th"$ transition. We also set $beta := beta - "spend"$. After fixing those 2, we recompute all the other constants and do the linear programming again till we consume the entire budget or $"un-fitness"$ becomes $0$.

=== Time Complexity

The algorithm one local change using linear programming and repeating again and again till the budget is consumed or the model becomes fit.

For the linear programming, given a petri net with $n$ transition, and a log with size $l$ we have to compute $2 l n + l + 3$ constants, which is $O(l n)$ time. Then we solve a linear programming problem with $n + l + 2$ variables and $3 l n + 2 l + 2$ constraints which can be computed in polynomial time (@LP-Complexity).

Now with all the budgets for $cal(N)$ computed, we can edit the petri net to get $cal(N')$ which has the higest possible fitness that can be achieved under the budget constraint $beta$.

// = Archive

// === Finding the Distance between the Model and the Log Traces

// During the execution of the model repair algorith, we keep updating the model, which means that the set of furthest log traces might change, hence we need to keep track of all the traces.

// We define the distance between a trace and a model as the minimum distance between the trace and any word of the model.  For that we would have to compute 1 + 1 + 1 +

// #definition([
//     *Definition 18:* The _flow function_ (or simply _flow_) of a trace is $f : (Sigma, RR^+)^*$ which keeps track of the delay between successive events and is defined for $tau =tau_1 tau_2 ... tau_n$ as $f = f_1 f_2 ... f_n$ where
//     #math.equation(block:true, numbering: none)[
//     $
//         f_i := cases(
//             tau_1 &i=1,
//             tau_i - tau_(i-1) quad quad quad&i in [2 ... n]
//         )
//     $
//     ]
// ]) <def18>

// Let the sequence of transitions in $cal(N)$ be $T = {t_1, t_2, t_3 ... t_n}$ where each $"SI"(t_i) = angle.l s_i, e_i angle.r$.
// Given a trace $tau = tau_1 tau_2 ... tau_n$ we can say it's distance from $cal(N)$ can be given by the following.

// Given a trace, we first find its flow and then we can use that to easily compute it's distance from the model in the following way.

// #algo(
//   title: [                    // note that title and parameters
//       #set text(size: 10pt)   // can be content
//       *Algorithm 1:* Dist
//   ],
//     parameters: ([$cal(N)$ : net],[$f$ : flow]),
//   comment-prefix: [#sym.triangle.stroked.r ],
//   comment-styles: (fill: rgb(50%, 50%, 50%)),
//   indent-size: 15pt,
//   indent-guides: 1pt + gray,
//   row-gutter: 5pt,
//   column-gutter: 5pt,
//   inset: 5pt,
//   stroke: 2pt + black,
//   fill: none,
// )[
//     $"n" := f."length"()$\
//     $"dist" := 0$\
//     for $i$ in $1 ... "n"$: #i\
//       if $f_i < s_i$ #i #comment[Transition taken too early]\
//         $"dist" := "dist" + (s_i - f_i)$ #d\
//       else if $f_i > e_i$ #i #comment[Transition taken too late]\
//         $"dist" := "dist" + (f_i - e_i)$ #d\
//       else #i #comment[Transition taken on time]\
//         $"dist" := "dist" + 0$ #d #d\
//     return $"dist"$
// ] <alg1>

// This can be done for each trace in $L$.\
// Now that we have a the set of logs we find the subset of the that are furthest away from the model which can simply be given by
// $
//     L_("max") = { sigma in L | forall sigma' in L, "Dist"(sigma, cal(N)) >= "Dist"(sigma', cal(N)) }
// $



// === Finding the Optimal Changes to Transitions

// We want to mimize out budget for a giving change in the fitness of the model, there are a few thigns that we need to keep in mind for that.
// - The fitness is only affected by log traces that are furthest away from the model.
// - If we want to make a change to transition, which affects some of furthest traces, but not all, it will not change the fitness, as the unaffected trace is still equally far away. So we would like to divide the budget to deal with multiple log traces at once.

// Note that we can say that improvement in fitness is $min$ of improvments in each trace. And improvement in a trace $tau$ is just the sum of budgets assigned to the transitions that affect the distance of $tau$.

// - For dealing with all boundaries at once, we define $B = {s_i | angle.l s_i, e_i angle.r in T} union {e_i | angle.l s_i, e_i angle.r in T}$
// - The above statement about boundaries affecting traces can be formalized as
// $
//     "is_affected_by"(tau, b) = cases(
//         top quad quad quad &b = e_i "and" e_i < tau_i,
//         top quad quad quad &b = s_i "and" s_i > tau_i,
//         bot &"otherwise"
//     )
// $

// We can rephrase our problem of finding an optimal distribution as a linear program, we define use the following definitions for it:

// - for each trace $tau_i in L'$ we have a variable $"tr"_i$ which represents how close the trace gets after making the edit.
// - for each $b in B$ we have the variable $"ch"_b$ which represent the portion of the budget assigned to that bound. Then we get the following equation for each $tr_i$.

// $
//     tr_i = sum_(b in B\ "is_affected_by"(tau_i, b) = top) "ch"_b
// $

// And we can measure the overall improved by the varible $"improvement"$ which can be given the constraint for each $tau_i in L'$
// $
//     "improvement" <= tr_i
// $

// Now for are linear program we just need condition
// $
//     max("improvement")
// $

// There are 3 extra constraints that we need to put that the algorithm does not ask us to spend an infinite amount of budget, these constraints correspond to the conditions when we need to stop spending the budget.

// - We cannot spend more than the budget
// $
//     sum_(b in B) "ch"_b <= beta
// $
// - We not to re-evaluate the updates each time an edit to a transition makes makes a trace be valid at some point.
//     - To do that, forall all $tau in L$, we define it's distance $d_(tau, b)$ from a bound $b$ as
//         - $0$ if it not affected by it.
//         - Distance between $f_j$ and $t_j$ where $f$ is the flow function of $tau$ and $t_j = angle.l dash, b angle.r "or" angle.l b, dash, angle.r$
//     - And $forall tau in L$ and $forall b in B$, if $"is_affected_by"(tau, b)$ we add the constraint
// $
//     d_(tau, b) >= "ch"_b
// $
// - We need to consider new transitions when they join the set of furthest transitions
//     - For every $tau_i in L$ (note: previously we were only dealing with $L'$) we define
// $
//     "tr"_i = sum_(b in B\ "is_affected_by"(tau_i, b)=top) "ch"_b \
//     "and" \
//     D - "improvement" >= "Dist"(tau_i, cal(N)) - "tr"_i
// $
// where $D$ is the maximum distance of a log trace from $cal(N)$.

// Finding a solution to the above linear program gives an edit for the petri net, and the change in the fitness which is $"improvement"$.

// === Editing the Petri Net

// Now we go over all $"ch"_b$
// - If $b = e_i$, then we set $e_i <- e_i + "ch"_b$
// - If $b = s_i$, then we set $s_i <- s_i - "ch"_b$
// - We also set $D <- D - "improvement"$
// - We update the budget $beta <- beta - sum_(b in B) "ch"_b$

// And we keep repeating this process until our budget goes down to zero.
