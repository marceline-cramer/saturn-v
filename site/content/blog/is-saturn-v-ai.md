+++
title = "Is Saturn V AI?"
description = "On artificial intelligence, disability, and rocket engines."
date = 2025-12-12
authors = ["Marceline Cramer"]

[extra]
giscus = true
+++

Short answer: yes — but not in the way you may expect.

# Generative and Symbolic

There's **generative AI**[^gen], which is what large language models (LLMs)
like ChatGPT, Gemini, and Claude are. How generative AIs work is by creating
a *statistical model* of some collection of data and using that model to
create new data that matches the patterns it finds. These definitely count as
"artificial intelligence" and have their own place within the field. However,
the field is much, much broader than just generative AI.

[^gen]: [Generative AI on Wikipedia](https://en.wikipedia.org/wiki/Generative_artificial_intelligence)

For instance, there's **symbolic AI**[^sym], which is what Saturn V is. The
term "symbolic" can be rather abstract, but just know that it uses *logic* as
opposed to massive datasets. Instead of feeding a symbolic AI examples of how
to act in different scenarios, you explicitly tell the AI how to act. Symbolic
AIs are therefore much more reliable than generative AIs, because they can only
make decisions within the confines of their programming. They also don't rely on
training data because their programming determines how they behave.

[^sym]: [Symbolic AI on Wikipedia](https://en.wikipedia.org/wiki/Symbolic_artificial_intelligence)

Historically, the vast, vast field of artificial intelligence was most
interested in symbolic AI rather than generative AI. Researchers could construct
more and more elaborate ways of instructing computers how to do complex tasks.
However, the problem with symbolic AI is that it is pretty bad at dealing with
the unexpected or ambiguous aspects of real-world problems. If an AI doesn't
know how to deal with a problem, a generative AI could hallucinate but a
symbolic AI will tell you "does not compute" and give up. A major limitation
of symbolic AI is that it's quite *brittle*: in order for symbolic AI to
handle all scenarios, humans must prepare it for those scenarios in advance.
Once technology that could adapt to unexpected inputs like neural nets became
practical in the 1990s, that approach has dominated the field since.

Nowadays, the term "AI" means "generative AI" to most people, and symbolic AI
has become much more obscure. However, I think that symbolic AI has never been
more important. There are many AI researchers who are trying to make generative
AI models hallucinate less. But think about it this way: why would you expect a
character in a book to realize that they're in a story? All generative AI sees
is raw data. People are trusting generative AIs to more and more aspects of
their life, but there are no guarantees that it will behave or follow the rules.

Generative AI still has its uses. For instance, one major problem that symbolic
AI does not have an easy answer to is how to get computers to understand natural
language. Spoken languages cannot be modeled purely logically because their
rules can and will be broken constantly by human users. LLM stands for large
*language* model, and regardless of their ability to support facts, they are
*extremely* good at interpreting the gray area in spoken languages. I'm very
excited to take advantage of that with Saturn V and to build practical natural
language interfaces to it.

However, LLMs are still *only* language models. I don't want the program in
charge of planning out my life and routines to just make decisions, I want
the program to make **good** decisions, according to *what I say is good*.
Generative AI is based on a lot of data, but not all of it is data *about me*.
If Saturn V is a prosthesis for habits, I don't want it to behave like it's
someone else's.

# AI and Disability

This brings me to the wider topic of *critical disability theory*, which is the
study of how disability relates to society. One major takeaway from disability
theory is that disability is *relative*. Instead of looking at disabilities just
as medical conditions, critical disability theory studies the social reasons
of why those disabilities prevent functioning in society in the first place.

For instance, one of my disabilities is that I am ADHD. I have a diagnosis and I
take stimulant medication to help me adapt. It's one reason I'm having Saturn V
help out my decision-making. However, it's important to note that *I* am the one
adapting to *today's* society. How come?

> However, as a result of the astonishingly fast cultural evolution of the
> human species and subsequent environmental changes, particularly in the last
> 10,000 years, ADHD traits have become maladaptive in present-day societies,
> and are therefore evolving to meet the demands of current environments. One
> of these theories, the hunter-farmer theory, states that ADHD traits specific
> to hunter-gatherers would have been environmentally beneficial well into the
> Neolithic Revolution, when non-ADHD traits characteristic of agriculturalism
> spread. Under this view, current humans diagnosed with ADHD should be enriched
> in alleles from ancient hunter-gatherers. [^adhd]

[^adhd]: [*Genomic analysis of the natural history of attention-deficit/hyperactivity disorder using Neanderthal and ancient Homo sapiens samples*](https://pmc.ncbi.nlm.nih.gov/articles/PMC7248073/). Esteller-Cucala, Maceda, Børglum, Demontis, Faraone, Cormand, Lao. doi:10.1038/s41598-020-65322-4.

For my neurodivergent comrades who *definitely* skimmed that quote, there is
genetic evidence to support that ADHD was actually beneficial in the context
of hunter-gatherer societies. But generative AI isn't trained on the data from
hunter-gatherer societies, it's trained on the data produced by the societies
that are eliminating the ADHD phenotype in the first place! So why should I
trust it to tell me what's good for ADHD or not?

# AI and Power

It can be easy to see ADHD (and other disabilities) as "problems" to "fix." If
I would have been considered fully-functioning by pre-agricultural times, that
certainly makes the idea of "fixing" my ADHD sound much less acceptable, doesn't
it? But if I developed Saturn V purely as a product or application, in the
traditional sense of the words, this is what would happen. Products are made to
*fulfill needs*, but for the sake of respecting the reality of my "condition,"
I've decided that I don't *need* to be fixed. Prostheses should *empower* their
users, not merely tolerate them.[^freedom]

[^freedom]: This is the shift from *negative freedom* to *positive freedom*. Murray Bookchin's essay [*Social Anarchism or Lifestyle Anarchism*](https://theanarchistlibrary.org/library/murray-bookchin-social-anarchism-or-lifestyle-anarchism-an-unbridgeable-chasm) is directly pertinent to this topic, but I'm not going to get into it here.

In practice, seeing Saturn V as an empowering prosthesis has
overarching consequences on its design. Saturn V is [malleable
software](https://www.inkandswitch.com/malleable-software/), meaning
that instead of inviting users to adapt to a way of using the tool, it
encourages them to adapt the tool to their needs. This is why [Saturn V is
free software](@/blog/why-free-software.md) and why I'm putting my effort
into developing Saturn V as an entire logic engine as opposed to a scheduling
application. I'm a user, too, and I'm not always going to have the same
opinions on how my habit prosthesis should work. Building and consolidating a
monolithic, opinionated product is *one* way to make a tool, but like
a hunter-gatherer, I prefer the nomadic approach. Using symbolic AI instead of generative AI is just another aspect of the same idea.

# Conclusion

That's why I built Saturn V using symbolic AI rather than generative AI. This
decision represents how I think about my profession, ideals, and mental health.
If AI is going to shape how we live, I want it to expand my freedom, not
manipulate it.

So... if Saturn V can't be considered strictly necessary, then
why do I put so much effort into building it? Well, [JFK put it
best](https://en.wikipedia.org/wiki/We_choose_to_go_to_the_Moon) when he made
the speech that rallied the Apollo program and eventually led to the development
of the [Saturn V launch vehicle](https://en.wikipedia.org/wiki/Saturn_V).

> We choose to go to the Moon in this decade and do the other things, not because
> they are easy, but because they are hard; because that goal will serve to
> organize and measure the best of our energies and skills, because that challenge
> is one that we are willing to accept, one we are unwilling to postpone, and one
> we intend to win, and the others, too.

---
