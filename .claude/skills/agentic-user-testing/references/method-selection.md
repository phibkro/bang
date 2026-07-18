# Method selection and evidence boundary

Choose the method from the decision and evidence needed, not from tool availability.

## Traditional research methods

| Method | Best evidence | Typical execution | Agent fit |
|---|---|---|---|
| Moderated task-based usability test | Where and why likely users fail, hesitate, recover, or misunderstand | Recruit representative users; give realistic neutral tasks; observe think-aloud behavior; probe sparingly; score outcomes; iterate | High as inspection/rehearsal, not as human validation |
| Unmoderated benchmark | Completion, time, abandonment, and version comparisons | Use fixed tasks and large enough samples with objective success states | High for deterministic replay; no human prevalence estimate |
| Contextual inquiry / field observation | Real workflows, interruptions, constraints, artifacts, and workarounds | Observe and interview users where work happens | Low; an agent lacks lived and embodied context |
| In-depth interview | Needs, language, past behavior, motivation, and mental models | Ask open questions and probe concrete past events | Low; synthetic biography and introspection are generated text |
| Diary / longitudinal study | Experiences unfolding over days or weeks | Repeated in-context entries and artifact capture | Low for human experience; useful only for system-state simulations |
| Survey | Population attitudes and subgroup distributions | Sample a defined population with a validated instrument | Very low without calibration to real respondent data |
| Card sorting / tree testing | Grouping, naming, and findability | Ask representative users to organise or locate content | Medium for vocabulary stress tests; low for population inference |
| A/B test and analytics | Causal behavior change and live funnels at scale | Randomise real traffic; analyse predefined outcomes | Agents may preflight variants but cannot replace real traffic |
| Participatory design | Solutions shaped with affected people | Co-create concepts and requirements with participants | Low; agents cannot represent stakeholder legitimacy |
| Heuristic evaluation / cognitive walkthrough | Predicted usability and learnability problems | Experts inspect against principles and action/feedback questions | High; this is the closest epistemic analogue |
| Accessibility audit and disabled-user testing | Conformance plus actual assistive-technology barriers | Expert audit, then sessions with disabled users on their setups | Agents can automate checks; cannot replace disabled users |

Use mixed methods. Interviews or contextual inquiry establish the problem; task tests diagnose the
interaction; analytics or benchmarks estimate frequency and trend; repeated rounds test improvements.

## What agents are effective at

Prefer agent sessions for:

- CLI, API, documentation, and developer-tool workflows with machine-verifiable outcomes;
- command and concept discovery from a controlled public source boundary;
- error diagnosis, recovery, malformed input, and adversarial variants;
- cognitive-walkthrough questions about goal visibility, action discoverability, and feedback;
- rapid replay after changes and cross-version regression inspection;
- piloting task wording and finding answer leakage;
- testing products whose intended users include coding agents.

Do not use them as substitutes for:

- authentic preference, demand, trust, adoption, willingness to pay, satisfaction, or emotion;
- embodied, social, cultural, organisational, accessibility, or longitudinal experience;
- representative demographic or behavioral distributions;
- causal or prevalence claims about people;
- unexpected needs outside the model's training and supplied context.

Common threats are training-data contamination, excessive technical competence, prompt sensitivity,
sycophancy, stereotype amplification, variance collapse, invented introspection, and pseudo-replication.
A fluent trace can be believable while behaviorally wrong.

## Evidence basis

- ISO 9241-11 frames usability in a specified context through effectiveness, efficiency, and
  satisfaction: <https://www.iso.org/standard/63500.html>
- GOV.UK's moderated-testing manual describes representative recruitment, neutral believable tasks,
  think-aloud observation, restrained intervention, and iterative analysis:
  <https://www.gov.uk/service-manual/user-research/using-moderated-usability-testing>
- GOV.UK recommends roughly 4–8 participants per formative round and hundreds for surveys,
  A/B tests, or benchmarks: <https://www.gov.uk/service-manual/user-research/plan-user-research-for-your-service>
- Nielsen and Landauer model problem discovery across iterative usability studies; their assumptions do
  not make “five users” a universal adequacy rule: <https://doi.org/10.1145/169059.169166>
- SimUser shows task-grounded LLM simulation can generate useful mobile-prototype feedback, while its
  validation is domain- and setup-specific: <https://doi.org/10.1145/3613904.3642481>
- UXAgent positions simulated interaction as study pretesting before human-subject research:
  <https://arxiv.org/abs/2504.09407>
- A 2026 systematic review of 182 studies finds inconsistent human fidelity and recommends treating
  synthetic participants as heuristic supplements: <https://www.researchsquare.com/article/rs-9057643/v1>
- SimulatorArena demonstrates that simulator reliability is task-dependent and must be calibrated to
  human conversations and judgments: <https://aclanthology.org/2025.emnlp-main.1786/>
- Persona variables often add only modest predictive value and work best where those variables truly
  explain human variation: <https://aclanthology.org/2024.acl-long.554/>
- Large-scale experiment replications show effect-size inflation and weaker performance on null and
  socially sensitive findings: <https://www.nature.com/articles/s43588-025-00840-7>
