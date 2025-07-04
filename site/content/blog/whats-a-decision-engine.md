+++
title = "What's a decision engine?"
description = "What's this \"decision engine\" I keep yapping about (and what is Saturn V anyway)?"
date = 2025-06-14
authors = ["Marceline Cramer"]

[extra]
giscus = true
pinned = true
+++

# Decision fatigue

Making decisions is hard. What to eat for breakfast? What clothes do I wear? Do I need to bring a coat? What homework do I need to do? Do I need to go shopping? These decisions add up, and there is a limit to how many good decisions a person can make in a given timespan. When this limit is reached, it is called [decision fatigue](https://www.ama-assn.org/delivering-care/public-health/what-doctors-wish-patients-knew-about-decision-fatigue).

A massive amount of effort every day is expended on making these very small decisions. To many, this becomes a point of self-expression: developing a fashion sense, cooking unique and fresh food at home, or developing personalized diets to suit their body goals. However, in the information age, the number of decisions we make on a daily basis is [massively rising](https://finance.yahoo.com/news/exhaustion-modern-life-decision-fatigue-180410366.html). Soon, everyone will need to have to carefully tailor their internet hygiene, routines, work schedules, and housework around this upper limit in human executive function.

Many people are already severely affected by decision fatigue. To the depressed, autistic, ADHD, chronically fatigued, [spoonie](https://en.wikipedia.org/wiki/Spoon_theory), or other mentally ill or disabled person, even doing the bare minimum to participate in modern society is fatiguing. Many people do not even have the ability to replenish their decision-making energy after what most people consider to be a suitable rest period, leading to long-term or chronic decision fatigue. For neurodivergent folks, there are very few cultural support structures in place to help neurodivergent people to make their lives work for their brains. Decision fatigue is a major contributing factor to the status quo that society is simply not well-suited to the mentally ill or disabled.

# The decision engine

I personally am depressed, ADHD, and *very* autistic, leading me to have an idea. How many of these minor, day-to-day decisions can be simply automated away? After all, we live in an era with access to massive amounts of computing power per capita. Just how many decisions in modern life can be simply delegated to an algorithm? I call the hypothetical algorithm that can take on this responsibility a "decision engine." The idea is simple: most of the small choices we make are based on very simple rules with complex interactions between them. A sufficiently advanced computer program should be capable of making those choices if it was made aware of those rules and interactions.

If everyday tasks could truly be automated in the full context of the rest of someone's life, imagine what that could do for society. One way of thinking about it is as a "prosthetic habits" system, like a cybernetic implant that allows people to spend their scarce decisions on more important, productive, or valuable things than the minutiae. Disabled and neurodivergent people might find life much easier to approach and succeed at a higher number of personal and important goals. If self-reflection and mindfulness activities were integrated into the engine as well, it could generally elevate one's ability to respond to and support themselves in the environment around them. Adding new rules and options to the decision engine does not tax the engine like it taxes an individual, meaning that individual habits become much easier to commit to, and it may push the upper limit on how many self-enrichment activities can be committed to for even averagely-abled people.

A decision engine would, of course, have to be both extremely personalized and complex. There are many, many factors contributing to all of the minor events and tasks going on in one's life. Designing an algorithm to coordinate someone's entire life is an essence a data integration problem. Luckily, as of the Web 2.0 boom, data integration is arguably what computers are best at in the moment. The little decisions driving a single person's entire life are a drop in the bucket compared to what modern data centers process every single day.

# So where are they?

The decision engine and its potential to solve decision fatigue would clearly have a lot of wide appeal. So, why doesn't it already exist? I believe that the reason is because the state of the data processing technology that could implement a decision engine is both fragmented and alienated from the user.

Since the smartphone boom of the late 2000s, everybody wants to make "the killer app." Every app clamors for your attention and a download onto your device, and the result is that each individual app has diminishing returns on how much data processing and functionality it can offer alone. This app overpopulation becomes yet another axis of decision fatigue because now *you*, the user, are responsible for coordinating all of these loud, bratty, antisocial apps into a meaningful whole. There are meal planner apps, grocery list apps, calendar apps, and video call apps, but there isn't an app that can remind you to buy bananas today because otherwise you won't have time for breakfast before your 6:00 AM Zoom meeting.

Despite the fact that the technology to augment entire lives exists, it is not being applied towards that end. In fact, it leads to the opposite: data analytics are the crux of social media, targeted advertising, and browser tracking technologies. These are the very things that are causing this pandemic of decision fatigue in the first place. To the average consumer it's a chronic inconvenience and to the disabled it's life-destroying. Google and Microsoft attempt to build the "super-app" to some extent through their own suites of integrated productivity tools. However, how personal, private, or modular could such a thing be? These massive companies profit off of your poor executive function in the first place, so why should they care about your 5:30 AM banana?

The solution to this is not something that the app market or Silicon Valley hype could accomplish on its own. *You have to give the technology back to the people.* By making the decision engine [free software](https://en.wikipedia.org/wiki/Free_software), [self-hostable](https://en.wikipedia.org/wiki/Self-hosting_(web_services)), and as modular as possible, it transitions from a hypothetical super-app to a practical system I can design. If it is licensed under a strong [copyleft](https://en.wikipedia.org/wiki/Copyleft) license, this guarantees that the community of decision engine users can maintain compatibility with each other, building an open network of people sharing their decision-making profiles with each other. It also rescues the decision engine from falling back into the same sort of app developer fragmentation.

# Summary of decision engines

Let's recap everything thus far. The decision engine needs to be:
1. **Personal**: The engine is supposed to be a cybernetic implant, right? Every user needs to have an extremely high degree of customizability over their own instance of the decision engine. All of your own weird lifestyle quirks should be a joy to factor into the system, not a nuisance.
2. **Modular**: The decision engine is supposed to be for everyone, so it needs to support an unbounded amount of extensibility. Any specific top-level design decisions would be presumptive at best or alienating at worst. I'm sick of apps following "good app design" in a little feature sandbox and limiting what I can do with them.
3. **Networked**: Making healthy, context-aware decisions requires a vast wealth of information about your own situation. It is critical that the decision engine is capable of integrating with arbitrary sources of external data such as calendars, map information, weather forecasts, or food prices.
4. **Open**: You're going to be putting all sorts of personal data into this thing, maybe even secrets you wouldn't tell anyone else. It should run on hardware you have access to and you should have a guarantee that it is not instrumented into some corporate data analytics system.
5. **Free**: If the decision engine becomes privatized and its inner workings are hidden from its users, all of the prior points are at risk of compromise. Strong free software licensing and a tightknit userbase demonstrating solidarity towards this end are critical. My thoughts on this subject are elaborated on in [Why free software?](@/blog/why-free-software.md)

# Introducing Saturn V

The decision engine is the core idea behind Saturn V: a piece of software that can be arbitrarily extended with rulesets reflecting the mechanics of a user's personal life, then make recommendations towards what decisions will meet that user's personal goals. To not get too technical, Saturn V is designed to support changing the rulesets and provide new information about the user's life at any time, making it an always-on decision-making companion.

Saturn V is a prototype. A decision engine that could be considered "complete" by majority consensus is well out of the scope of any piece of software that I can create alone (for free). My main focus for Saturn V is to make a decision engine that supports *my* needs as a first priority, simply because I'm incapable of making anything else (especially for free). However, I also make an effort to share my work whenever possible. Saturn V is licensed as [free software](https://en.wikipedia.org/wiki/Free_software) and its development is done publicly on [its GitHub repository](https://github.com/marceline-cramer/saturn-v). I hope that in time, future decision engines will be created using different design approaches than mine. Saturn V is made for me first, as a research project second, and as a consumer-targeted app third. There will come a day where a design aspect of Saturn V becomes untenable with its goals, in which case a new decision engine project will need to be launched to advance decision engine development to the next stage.
