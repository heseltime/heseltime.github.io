---
layout: Post
permalink: /portfolio
title: Portfolio
feedformat: none
---

With a DevOps background I broke into Software Engineering, benefiting from [formal training in the subject](/rDse) on top of long-time programming (since middle school), and with multi-year experience in Enterprise Content Management (ECM) and my own initial hobby Single Page Applications (SPAs) sprinkled in there, I have made this my professional work: my model for implementation is workflow-oriented, modern ECM (think Alfresco and Activiti/Camunda) coupled with high-level analytics (think Wolfram Language, i.e. really high level). At the same time, I realize Software Engineering is many different approaches, so in the below I reference this where appropriate and explore the ways I can apply my skillset across paradigms.

<div class="toc" id="jku-thesis-project">
    <h2>core project (academic software development)</h2>
    <h4>Masters thesis project at Johannes Kepler University (JKU), consisting of the following research components leading up to the technical report (project) and thesis</h4>
    <p>I'd like to thank the <a href="/notes">wonderful Update Social Team (on-going notes included)</a> in helping to refine this project up to an actionable starting point, and <a href="https://github.com/heseltime/updatesocial">reference the repo for initial testing and prototyping</a>.</p>
    <h3>PDF-Metadata Extraction and Feedback Plattform (Forthcoming?)</h3>
    <p><b>0.</b> It would be exciting to spin this work out into something available to anyone who might be interested in the future: I'll reserve the rest of the summer of 2025 and ff., once the thesis is done, for this, if I can.</p>
    <h3>LLM Processing and Evaluation of the Output (Forthcoming)</h3>
    <p><b>1.</b> Main Thesis work (55-65p). <i>Emerging structure:</i></p>
    <ul> 
        <li>10p.(+?) <i>General LLM Tasks/Few-Shot <b>Intro</b>, see also seminar presentation, and make connection to</i> Update Social (see LIFT_C below) <i>as a way to introduce the current applications landscape and challenges</i> In the final structure this part is broken down (Intro, Concepts and Definitions, Legal Context, Related Work)</li>
        <li>15p. <i>Practical-Work-takeaway: <b>Technical framework</b> for pipeline-development</i> In the final structure: "Solution Design"</li>
        <li>20p. <i>Main Research part: <b>Evaluation</b> of LLM applications, SOTA, chosen approach, round out current theory. <b>Idea for first section</b>: start with the idea for LLM-automating the scoring mechanism tasks currently requiring manual input. Evaluate those against manual scoring. See if and how this approach can be extended to the overall goal of document-transformation for accessibility. An exploration of completely LLM-based scoring might be interesting here (but is probably not required as a focus of this work).</i> In the final structure: "Methods and Data"</li>
        <li>5-10p. <i><b>Implementation</b>: Overview, some technical details and code - for the AI part, in contrast to the practical work (system part)</i></li>
        <li>5-10p. <i><b>Results</b>: Discussion, pick up evaluation (of the whole project), future work</i></li>
    </ul>
    <a href="../../assets/pdf/JKU_AI_Masters_Practical_Work_Report_SS2025__hoffman_-1-1.pdf"><h3 id="jku-practical-work">Standard Software Integration (Enterprise Content Management - ECM, Done!)</h3></a>
    <p><b>+.</b> It is actually possible to extract this part out of the main academic work, and so I am starting here, for a <b>practical work component in my Masters</b>.</p>
    <img src="/assets/img/linkedin/hoffman-thumb.webp" alt="Dr Hoffman from Angela Carter's The Infernal Desire Machines Inspires This Work" />
    <p><b>From the Abstract</b>: <i>This Practical Work Report details the selection and configuration of a modern GenAI (Generative AI)/ECM (enterprise content management) framework for optimizing the PDF document processing required to annotate and tag content to make it readable for screen-reader and related software. The goal is to create a portable module, on the one hand, where this Practical Work effort was also supported - by way of introduction the Alfresco ECM system and practical experience with the technology - by FAW GmbH, a company specializing in ECM product customizations in Hagenberg, Austria, and to provide a setup for efficient document processing and evaluation at a more involved level, leading to a Masters Thesis at JKU in Linz. Test-runs on an initial dataset demonstrating the applicability of LLMs (large language models) and particularly a self-hosted setup in addition to an API-based one complete the proof of concept, for using LLMs in either the few-shot in-context learning or the fine-tuning regime to make documents barrier-free and accessible.</i></p>
    <p><b><a href="../../assets/pdf/JKU_AI_Masters_Practical_Work_Report_SS2025__hoffman_-1-1.pdf">Report done!</a></b></p>
    <p><b>Update</b>: Worked on this as part of the <a href="/note/Mistral-AI-x-a16z-London-Hackathon-2024">Mistral AI x a16z London Hackathon 2024</a>, extending the accessibility buddies idea below!</p>
    <a href="https://docs.google.com/presentation/d/18mkzttmRAo7kTcdBRxyERATSdmqt9ODidUBlRLN30Mg/edit#slide=id.gcb9a0b074_1_0"><img alt="PDFStral Pitch Deck" src="../../assets/img/PDFStral-deck-coverslide.png" /></a>
    <p>In the language of this portfolio, this scripting project (Software Engineering view of Machine Learning (ML): all scripting, right?) marks an ML departure. It also build on an <a href="#open-ai-api">initial OpenAI API Test involving transformation of a collection of daily reports to one monthly report</a>, demonstrating a summarization ECM use case.</p>
</div>

## <a name="postit-u"></a> ["In Linz beginnts!" - PostIT:U](https://postit-u.at)

"It starts in Linz" - here is project I doubled for my roles in, one as fullstack engineer (hence inclusion in this portfolio) developing an [older project](#postcity) into something new, and second as KHJ (Catholic University Youth in Upper Austria) Head of the Board/IT:U Founding Lab Member, aiming to tell the story of finding this new university's location from the student perspective, (a), and (B), for Bolitics, holding the officeholders accountable, come January 12th (2025) Linz Mayoral Elections, by collecting their statements/positions _before_ the election.

[![NextStop API Overview with Swagger](/assets/img/postitu-header-screengrab.png)](https://postit-u.at)

## <a name="next-stop"></a> NextStop (KHG)

This is a Hagenberg project adapting the [REST API exercise class project](https://github.com/heseltime/SWK5-ue7-OrderManagement-) for the Component-Oriented Software Engineering Course (focused on .NET). The basic idea was to take the bus stop project requirement and apply it to an event management system idea for [KHG](/khg), attempting visualize goings-on in-house using a bus schedule metaphor.

![NextStop API Overview with Swagger](/assets/img/next-stop-api-swagger.png)

More details in the [Readme](https://github.com/heseltime/SWK5-NextStop-AS1-alt). 

### Frontend

The frontend illustrates how the endpoints shown above are operationalized to the users: info-screens, bus drivers (check-ins), as well as bus company management roles.

(Upcoming.)

## [PDFstral.london](pdfstral.london)

See <a href="/note/Mistral-AI-x-a16z-London-Hackathon-2024">Mistral AI x a16z London Hackathon 2024</a> - the <a href="https://pdfstral.streamlit.app/">output</a>:

[![PDFstral Python Stack Document Accessibility Explorer](/assets/img/PDFstral-screengrab.png)](https://pdfstral.streamlit.app/)

## LIFT_C

The technical continuation to a thesis is the result of a group project at [LIFT_C](https://www.jku.at/lift-c/) @[JKU](https://www.jku.at/en), see the [research feed for this](/_notes) and [this cute roll-up](https://heseltime.github.io/note/AB-Roll-Up-Design):

![Roll-Up Design Accessibility Buddies](/assets/img/rollup.png)

# <a name="it-u"></a> [IT-U](https://it-u.at/en/) Software Engineering Part for Interdisciplinary Installation Project

This was a cute little project I was allowed to accompany in technical role resulting in a fairly original installations setup running on multiple raspberry pis and a local network, plugging into the global seismographic network in turn, making it audible at a human ("totem") level at a newborn university's temporary home inside Linz/JKU Science Park - the context was a summer school offered in 2024, the project team an interdisciplinary group (one visual artist, one humanities researcher, one natural scientist, me in the capacity of the dev), affording learning mostly in this small-group, trans-disciplinary, self-organized dimension, though working with raspberry tech and sonification technology was new to me, on the technical one.

![IT:U Poster](/pages/inter_totem-poster.png)

# <a name="open-api"></a> Hagenberg Software Engineering Final Java Project: Spring Boot (Spring Data, Spring MVC) and React Marketplace App

## Outline

```
+------------------+    +-------------------------------------------------------+
|    Frontend      |    |                         Backend                       |
|                  |    |                   |               |                   |
|  +--------+      |    | PresentationLayer | ServiceLayer  | PersistenceLayer  |
|  | WebApp |      |    |                   |               |                   |
|  | Model  |      |    |                   |               |                   |
|  | HTML   | -----+--> | Controller    DTO |   Service     | DAO/Repo  Entity  |
|  +--------+      |    |                   |  Components   |                   |
|                  |    |                   |               |                   |
|                  |    |                                                       |
+------------------+    +-------------------------------------------------------+
```

## Schema and API Design

The Swagger OpenAPI Schema view:

![Swagger Schema View](../assets/img/swt6/Screenshot%202024-05-21%20101948.png)

Swagger UI - **Before Annotation**:

![Swagger UI representation of the Controller endpoints](../assets/img/swt6/Screenshot%202024-05-21%20003320.png)

**After Annotation** in the source code:

![Swagger UI representation of the Controller endpoints with annotations](../assets/img/swt6/Screenshot%202024-05-21%20102000.png)

## Result (Screenshots of the frontend)

This was mainly a Spring Boot API project, so I would actually say the annotated Swagger OpenAPI document is the main output of this exercise. That said, here are the screenshots of a lightweight frontend:

![Frontend 1](../assets/img/swt6/Screenshot%202024-05-21%20101758.png)
![Frontend 2](../assets/img/swt6/Screenshot%202024-05-21%20101809.png)

**Update**: almost forgot search functionality.

![Frontend 2a](../assets/img/swt6/Screenshot%202024-05-21%20104257.png)
![Frontend 2b](../assets/img/swt6/Screenshot%202024-05-21%20104312.png)

![Frontend 3](../assets/img/swt6/Screenshot%202024-05-21%20101823.png)
![Frontend 4](../assets/img/swt6/Screenshot%202024-05-21%20101848.png)

## [Full Repo](https://github.com/heseltime/SWT6Marketplace)

All in all, this was a nice project drawing togeth Object Oriented programming, API design and a React frontend into a rapid development framework, since it had to get done fast. I think this kind of thing is the bread and butter in Software Engineering. But let's face it, the world is probably not quick to need yet another marketplace app.

## <a name="open-ai-api"></a>Scripting: Python OpenAI API Package Testing

Not as visual, but certainly useful (ties in with my [grad thesis](/rDai#jku-thesis-overview) too), therefore an honorable mention in my portfolio:

[![(Progress) Reports with the OpenAI API](image.png)](https://github.com/heseltime/progress-reports/)

[More details on this page](/curl) and just click the image above to go to the repo and instructions for your own setup, if interested - I think I will move scripting topics to my [rX feed](/notes) in the future. Scroll down for my team-engineering, visually appealing (I try) type stuff!

# Industry Partnership Hagenberg Software Engineering: ventopay/mocca Dashboard

[Ventopay](https://ventopay.com/) does full-service cantine systems targeting the DACH market: their flagship [mocca](https://ventopay.com/bargeldloses-zahlungssystem-mocca/mocca-software/) software became the platform for a ten-person student project in close partnership between [Hagenberg Campus](https://www.fh-ooe.at/campus-hagenberg/) and the company. Tasked with developing the status and notifcation system, I took on a hybrid role of product owner (PO)/developer, implementing the traffic light style overview page for example, but also going in type loops between team and company to provide effective POing.

## Screengrabs Iteration II (Spring '24)

The final project iteration was delivered on time, documented and evaluated (against ventopay's own review guidelines) in spring and further to this group's (ca. 10 members) graduation requirements in the [Software Engineering course in Hagenberg](/rDse). In a traditional Austrian manner, the finalized project was celebrated on-site in the countryside ([Mühlviertel](https://en.wikipedia.org/wiki/M%C3%BChlviertel)) to some beers.

<div id="ventopay-screenshots">
    <img src="../assets/img/Screenshot 2024-04-27 093139.png" alt="mocca screengrab 1" class="xxx-large" />
    <img src="../assets/img/Screenshot 2024-04-27 093150.png" alt="mocca screengrab 2" class="xxx-large" />
    <img src="../assets/img/Screenshot 2024-04-27 110830.png" alt="mocca screengrab 3" class="xxx-large" />
    <img src="../assets/img/Screenshot 2024-04-27 110853.png" alt="mocca screengrab 4" class="xxx-large" />
    <img src="../assets/img/Screenshot 2024-04-27 110921.png" alt="mocca screengrab 5" class="xxx-large" />
</div>

## Screengrabs Iteration I (Fall '23)


<img src="../assets/img/Screenshot 2024-01-20 144337.png" alt="mocca screengrab 2" class="xxx-large" />
<img src="../assets/img/Screenshot 2024-01-20 144320.png" alt="mocca screengrab 1" class="xxx-large" />
<img src="../assets/img/Screenshot 2024-01-20 144348.png" alt="mocca screengrab 3" class="xxx-large" />


## Note

The challenge with this project was that it is an acutal production product that was developed, so very far from green-field software development. Compare that to the following from-scratch engineering project.

# Angular Frontend Reference Project "SnackFrontend" ('24, #SoftwareEngineering: Frontend to an API with Some Authentication)

<div id="angular-leader">This is the frotend piece realizing the SNACK (think restaurants) <a href="#backend-endpoints">endpoints</a> designed and implemented in ASP .NET CORE the previous year. <a href="https://github.com/heseltime/SnackFrontend-reference-project">Full repo of the one-man, ca. 100-hour project</a> and project structure with some screenshots to demonstrate. </div>

I feel like this type of small-scale, but general, project lends itself to all kinds of use cases in terms of structure and design.

## Frontend App Structure

```
src
|-- app
|  |-- discover-restaurants <--- *route: /restaurants ---------------- user view of this app, main part: see assumptions.txt
|  |  |-- find-restaurants
|  |  |  |-- restaurant-detail
|  |  |  |  |-- order form
|  |  |-- my-orders
||||-- home <------------------- *route: /manage --------------------- restaurant view: authentication required
||||  |-- incoming-orders
||||  |-- my-restaurant with menu upload, and delivery condition/other info editing
|  |-- login
|  |-- register
|  |-- page-not-found
|  |-- shared
|  |  |-- discover-restaurants.service.ts
|  |  |-- discover-restaurants.model.ts?
|  |  |-- discover-menus.model.ts?
|  |  |-- discover-... .model.ts? - all the models in the end
|  |  |-- manage-restaurant.service.ts
|  |  |-- theme.service.ts - just for testing
||||-- app.module.ts incl. AuthModule for OpenID Connect/0Auth authentication with Auth0 (Okta - https://auth0.com/)
|-- styles.css, assets and environments
|-- index.html
```

## Screenshots

Boostrap and Fontawesome go pretty far as for design tools:

<img width="473" alt="Screenshot 2024-01-11 013545" src="https://github.com/heseltime/SnackFrontend-reference-project/assets/66922223/29bdeb11-3315-42a2-bf78-278f3a17a572">

<img width="473" alt="Screenshot 2024-01-11 013610" src="https://github.com/heseltime/SnackFrontend-reference-project/assets/66922223/08a54f6b-9a11-4c5f-90e6-ee8e1f2ac716">

Auth0 for authentication and user metadata:

<img width="480" alt="Screenshot 2024-01-11 013843" src="https://github.com/heseltime/SnackFrontend-reference-project/assets/66922223/aa3dd71a-4f17-4026-adc5-fe1bd89f9056">

Simple forms and form validations:

<img width="527" alt="Screenshot 2024-01-11 014714" src="https://github.com/heseltime/SnackFrontend-reference-project/assets/66922223/12e9080a-7859-41c3-852b-a1ed37c8a94e">

<img width="472" alt="Screenshot 2024-01-11 014702" src="https://github.com/heseltime/SnackFrontend-reference-project/assets/66922223/8ef80ec6-44eb-4482-b71e-b71a236a1572">

# Little React List App ('23, #SoftwareEngineering: Backend + Frontend)

<div id="react-leader">React testing after being more a Vue.js guy!</div>

Build tool: [Vite.js](https://vitejs.dev/guide/) Here a small-scale [view/list app](https://github.com/heseltime/WEA5-BookShopWithReact) with an [Express backend](https://github.com/heseltime/WEA5-ExpressBackend), simulating a bookstore.

<img src="../assets/img/Screenshot 2023-12-27 065838.png" width="100%">
<img src="../assets/img/Screenshot 2023-12-27 065905.png" width="100%">

# ASP.NET CORE Backend Reference Project "SnackBackend" ('23, #SoftwareEngineering: Backend API)

<div id="asp-leader">A full scale .NET project with a focus on clean layering, MVC pattern, authetnication and token handling.</div>


[Clone of the actual study project on GitHub.](https://github.com/heseltime/SnackAdmin-reference-backend-project)

<img src="../assets/img/Screenshot 2023-12-22 230644.png" width="100%" id="backend-endpoints">

Angular frontend project to follow, concluding semester 5 of an intensive [Software Engineering](/rDse) curriculum.

# <a name="postcity"></a> Der Standard Mock-up ('23, #ArsElectronica/#SoftwareEngineering: Some Experimental Frontend)

**Update**: Developed further to a public-facing political [project about IT:U (neé IDSA) location politics for the 2025 Linz Mayoral Election](#postit-u).

<div id="scrollytelling">See also <a href="/notes">rX Feed</a> and <a href="https://www.derstandard.at/promotion/velcom?DcIYkpda/idsa-eine-universitaet-beginnt#!/" target="_BLANK">the final piece published by Der Standard</a>, a high-end Austrian newspaper (my pretty face is in the header, if you can find me!) -  I delivered the below mockup for a scrollytelling, dynamic version with conveyor belts (the Ars Electronica Festival 2023 took place in an abandoned post (packages) processing plant) but Der Standard went with a simpler static design and layout (their loss!).</div>

Nevertheless I was involved in the writing and content as well, see <a href="/notes">rX Feed</a> again, for that part: I find the art-society-technology approach Ars Electronica takes to be a fruitful way to think new tech, to say the least.

## Screengrabs

<img src="../assets/img/derstandard/Screenshot 2023-10-09 104641.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104814.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104659.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104709.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104720.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104726.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104747.png" width="100%">
<img src="../assets/img/derstandard/Screenshot 2023-10-09 104756.png" width="100%">

## Features

* Vue.js project
* scrollytelling with Scrollama


# Classic Scripting Small-Scale Project (Vanilla PHP): Public-Private Pattern, Simple Database Connectivity ('23, #SoftwareEngineering: Scripting)

What it says on the tin! 

The project is fictional photovoltaics application portal, completed as part of a formal [Software Engineering](/rDse) (course: Scripting Languages/PHP-Web-Project) degree. 

<img src="https://user-images.githubusercontent.com/66922223/245513932-ae0379f5-cce3-43df-af7d-840b12b29282.png" width="100%">
<img src="https://user-images.githubusercontent.com/66922223/246044965-36aa6fa2-2e83-4fe6-8cb2-cf22b7594a35.png" width="100%">
<img src="https://user-images.githubusercontent.com/66922223/246044798-5ddc6087-85a9-46bc-90ea-9d71c7e5dad4.png" width="100%">

It's the stuff the web is made of, these small portal/applet-type things. [Full readme](https://github.com/heseltime/php-myseql-pv-assistance)

# ECM: D.velop Documents/Process ('20-23, #SoftwareEngineering: Process Design, Forms and Frameworks)

D.velop is a German company marketing a mid-tier ECM system that is now very common in the DACH region. It is often named in the innovative categories in Gartner Magic Quadrant because it is a well thought out system that nevertheless makes due with some legacy code and languages especially in their Workflow component (Flow Designer). The latter is being revamped though, as D.velop Process, on top of a Camunda Workflow Engine. Camunda itself is an (Alfresco) Activiti Fork.

This work took place for the Red Cross and is mostly confidential as such. I can share the following aspects of a three-year, multi-project engagement 2020-23.

## Projects

- The work was multi-departmental, from planning over modelling (BPMN) to execution with two external partners. I lead the internal code implementation: languges used were Java, Groovy, JavaScript, JPL (proprietary).
- The work had one important archiving component, using a third party tool that protects records (revision safe archiving, the tool is [Graudata](https://www.graudata.com)) and makes them conform to the hefty regularity requirements in the blood banking field.
- Most of the work was about expanding workflow-capability, i.e. automisation, in the documents arena, where documentation is a central aspect of blood banking. The most complicated workflow was a five-part (!) cycle including blood bank worker training, archiving of trainable documents, clear distinction of documents that are being worked on and documents that are valid and need to be known and documented as trained to all the relevant professionals, lab workers and doctors mainly, in the different departments. It also included a multi-stage signing step (for department heads/experts) to  guarantee validity of the documents that are being circulated in the blood bank and meet Austrian/EU regularity requirements of these documents: this gives an idea of the nature of the ECM approach and the topics in ECM in companies that are not typically thought of as "content companies," here in health and blood banking particularly. 
- The work saw a team expansion by a factor of three, all working on ECM in Linz blood bank. The ECM-commitment of the blood bank grew to hotline/support implementation dedicated to ECM, and internal trainings focussed around ECM. 
- The end of my tenure with the Red Cross saw the inception of the study project documented in the rX-section of this website: The goal of the project is to establish modern internal development workflows independent of external consultants and contractors to advance the quantity and quality of internal initiatives. I continue to stay involved on a volunteer basis and through this study project.

I owned all of the above initiatives in the capacity of a DevOps Engineer focussed on internal Softare Implementation.

# SPA: co2work ('22, #SoftwareEngineering: Lightweight SPAs)

[co2work](http://co2work.at) is an Upper Austrian co-working place lander with C02-Footprint calculator for social media sharing. 

## Screengrabs

<img src="../assets/img/Screenshot 2022-09-10 at 20.46.02.png" width="100%">
<img src="../assets/img/Screenshot 2022-09-10 at 20.46.46.png" width="100%">
<img src="../assets/img/Screenshot 2022-09-10 at 20.47.03.png" width="100%">

## Features
- vue SPA
- REST api integration of an external backend
- swiper.js for the form implementation

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