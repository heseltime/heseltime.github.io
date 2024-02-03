---
layout: Post
permalink: /curl
title: Proof of concept shell/curl LLM reporting and summarization tool
feedformat: none
---

# Let's Try Something Out

How about some more development-notes style entries on this website, perhaps for rX Feed? In any case here is a test LLM workflow python script with actual influence on my productive work, based on [my repo](https://github.com/heseltime/progress-reports/) with a more detailed [setup section](https://github.com/heseltime/progress-reports/tree/main?tab=readme-ov-file#heres-the-setup-wrench) in the README.

![(Progress | X) Reports with the OpenAI API](image.png)

## Use Case

([As per the repo README](https://github.com/heseltime/progress-reports/?tab=readme-ov-file#paperclip-progress--x-reports-paperclip-with-the-openai-api-postbox).)

I have a collection of daily reports in a folder somewhere, let's say they all follow the filename format "yyyymmdd.txt", so we know what month they pertain to, and I want to generate an LLM progress report mostly in third person, the type may or may not be asked for consultancy work or any job, here with a slant towards software engineering. 

I want to run a program that takes care of the content accurately but flexibly and in the style I like, even perform some simple summation (this type of math an LLM can currently certainly already do) of hours worked (included in the daily report), thus automating away the monthly task and also doing the simple by-handy tallying of (billable, typically) hours worked.

Daily report example (redacted):

>Daily Report with Time (Jack Heseltine) - Date: February 1st
>
>
>Daily Report
>
>
>Focused on PROJECT X Analysis after formalizing how to best troubleshoot with COLLEAGUE A on Monday: notes in JIRA-TICKET-NUMBER. As before, learning to track through client side, api side to DAO/entity layers and the table itself. Review meeting of analysis so far with COLLEAGUE A. Shift to developing a fix in a new ticket: JIRA-TICKET-NUMBER
>
>
>
>Open Question/Idea for Weekly Recap
>
>
>* "Needs Production Testing" field in jira tickets: general rule here?
>
>* COLLEAGUE A had an idea to do a Special Subclass Implementation (clean) version of the bug fix outlined in JIRA-TICKET-NUMBER which I like a lot.
>
>
>
>Time (hrs/category/work) February 1st
>
>
>* 3.5	analyze PROJECT A, move to status Developing
>* 1.5	meet COLLEAGE A to discuss JIRA-TICKET-NUMBER and intended fix
>* 3	start on new ticket JIRA-TICKET-NUMBER, make new branch, ant format-java-clean process for building and pushing for review with COLLEAGUE A on Friday.
>
>Total 8

So imagine 20 or so of these at the end of a month and now you need to submit your progress report. 

The output per month should be:

> Subject: Progress Report for Jack Heseltine - January 2024
>
>Executive Summary:
>
>January marked the initiation of Jack Heseltine's role as a Software Engineer Consultant at Wolfram Research. The month was primarily dedicated to onboarding and technical setup, followed by a deep dive into the Cloud Team's operations. Significant progress was made in familiarizing with the company's systems and tools, particularly Mathematica and the Cloud platform. Efforts were focused on completing the Newhire Checklist, resolving technical setup issues, and beginning work on specific Jira tickets related to cloud functionality.
>
>Details:
>
>1. Onboarding and Technical Setup:
>   - Completed the Newhire Checklist (18 items).
>   - Overcame challenges with tech setup including SOFTWARE builds, VPN, email, and local environment configurations.
>   - Successfully resolved multiple technical issues, documented in Jira (JIRA-TICKET-NUMBER).
>
>2. Learning and Development:
>   - Engaged in reading and understanding of the Cloud Team Handbook and related technical documentation.
>   - Began learning about THE Language and specific tools like THE Workbench/Eclipse.
>   - Attended meetings with senior team members for guidance and next steps, ensuring smooth integration into the team.
>
>3. Project Involvement:
>   - Started analysis on initial task set related to Cloud functionality (CLOUD-24255).
>   - Investigated and resolved database issues encountered during local setup.
>   - Engaged in detailed study of COLLEAGUE A's technical slides and API endpoints related to PROJECT X and PROJECT Y.
>
>List of Bugs/Tickets Completed:
>- JIRA-TICKET-NUMBER: Local setup and technical issues.
>- JIRA-TICKET-NUMBER: Initial analysis on PROJECT X. (Still in progress.)
>
>PTO:
>- Not applicable to consultant role.
>
>Data Sources:
>- Jira tickets (JIRA-TICKET-NUMBER, JIRA-TICKET-NUMBER)
>- Stash and TechDocs
>- Personal logs and meeting notes
>
>Total Hours Worked:
>- Week 1 (Jan 8 - 12): 32 hours
>- Week 2 (Jan 15 - 19): 30.5 hours
>- Week 3 (Jan 22 - 24): 23 hours
>- Week 4 (Jan 29 - 31): 24 hours
>
>Total 109.5

This is a manual, redacted progress report example, compare the LLM-example below! (Spoiler: The LLM one is just as good as my bored and haphazard effort at a slightly boring task, probably better.) It and other examples could be added to the prompt in few-shot learning manner, especially including pertinent details and ways to formulate and focus on certain aspects (see future steps below).

### Tools

Let's use the OpenAI python package to call the chat [completion API](https://platform.openai.com/docs/api-reference/chat). OpenAI also has a [quickstart tutorial](https://platform.openai.com/docs/quickstart?context=python) about this topic to get you up to speed, with a quick virtual environment/python installation primer included.

### LLM Point of View/Prompt Engineering

I chose diligent HR worker-type here but this could be anything you feel like you want. I added the important technical detail of not being judgy or providing "all-in-all" type sentences ("All in all, Jack tries really hard") because that is not appropriate for my use case, i.e. the judging is done by someone else.

## Implementation

Apart from the usual argument parsing making it convenient to call, offshoring some important details into a .env-file, etc. the meat of this little daily (monthly) helper is in the generate_report() function here, demonstrating how the OpenAI API chat completion call and return of the completion string, works:

```
def generate_report(year, month, temperature):
    # Access the API key from environment variables
    api_key = os.getenv('OPENAI_API_KEY')
    client = openai.OpenAI(api_key=api_key)

    file_pattern = f"{year}{month:02d}??*.txt"
    files = glob(file_pattern)

    # Concatenate the content of the reports
    reports_content = "\n\n".join(open(file, "r").read() for file in files)

    completion = client.chat.completions.create(
        model="gpt-3.5-turbo",
        temperature=temperature,
        messages=[
            {"role": "system", "content": """You are a diligent and objective HR professional. You have been asked to generate a report for the progress of the consultants in a software department, based on the daily reports submitted by the consultants themselves. 
             
            You trust their own judgement and try to be nice but fair and objective too, highlighting completed work but also mentioning potential challenges covered in the daily reports.

            Do not judge the consultant, do not include a summary "overall" paragraph at the end, and do not include any personal opinions. 

            The report is supposed to be in the following format:

            Subject: Progress Report for <FirstName> <LastName> <Month> 

            * audience: a mix of both executives, colleagues

            Suggested format:

            * executive summary paragraph, heading Executive Summary.

            * details section, the heading should be Details, you can add flexible sub-headings for
                * group by product or major area
                * do include details for benefit of colleagues here
                * think about impact of your work on others
                * list of bugs/tickets completed: Sub-Heading List of Bugs/Tickets Completed

            * mention days PTO, but say these are not applicable to consultants. The heading should be PTO.

            Data sources:
            * bugs and jira databases for tickets
            * sent email
            * PTO report/timesheets
            * Stash
            * personal logs
             
            Finally, sum together the hours worked per week and give an overall number of hours worked for the month so far. The heading for this part should be Total Hours Worked, then the weeks with their totals and ideally the dates of the start and the end of the respective week too, then the Total for the month below that.
            """},
            {"role": "user", "content": reports_content}
        ]
    )

    print("Completion usage information:\n", completion.usage)

    return completion.choices[0].message.content
```

<nav class="nav">
    <ul class="nav__list">
        <a href="/" class="nav__link">
            <i class="ri-home-5-line"></i>
            <span class="nav__name">
                Home
            </span>
        </a>

        <a href="/notes" class="nav__link">
            <i class="ri-swap-line"></i>
            <span class="nav__name">
                Feed
            </span>
        </a>

        <a href="/portfolio" class="nav__link active-link">
            <i class="ri-slideshow-2-line"></i>
            <span class="nav__name">
                Portfolio
            </span>
        </a>

        <a href="/rDai" class="nav__link">
            <i class="ri-robot-line"></i>
            <span class="nav__name">
                AI
            </span>
        </a>

        <a href="/rDse" class="nav__link">
            <i class="ri-command-line"></i>
            <span class="nav__name">
                Software
            </span>
        </a>

        <svg class="indicator" width="94" height="56" xmlns="http://www.w3.org/2000/svg">
            <ellipse cx="47" cy="28" rx="24" ry="28"/>
            <path d="M24 20C24 20 28 55.9999 48 56L0 55.9997C18 55.9998 24 20 24 20Z"/>
            <path d="M70 20C70 20 66 55.9999 46 56L94 55.9997C76 55.9998 70 20 70 20Z"/>
        </svg>
    </ul>

    <script src="{{ site.baseurl }}/assets-liquid-nav/js/main.js"></script>
</nav>