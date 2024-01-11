---
layout: Post
permalink: /portfolio
title: Portfolio
feedformat: none
---

With a DevOps background I broke into Software Engineering, benefiting from [formal training in the subject](/rDse), and with multi-year experience in Enterprise Content Management (ECM) and my own initial hobby Single Page Applications (SPAs) sprinkled in there, I have made this my professional work: my model for implementation is workflow-oriented, modern ECM (think Alfresco and Activiti/Camunda) coupled with high-level analytics (think Wolfram Language, i.e. really high level). At the same time, I realize Software Engineering is many different approaches, so in the below I reference this where appropriate and explore the ways I can apply my skillset across paradigms.

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

React testing after being more a Vue.js guy! Build tool: [Vite.js](https://vitejs.dev/guide/) Here a small-scale [view/list app](https://github.com/heseltime/WEA5-BookShopWithReact) with an [Express backend](https://github.com/heseltime/WEA5-ExpressBackend), simulating a bookstore.

<img src="../assets/img/Screenshot 2023-12-27 065838.png" width="100%">
<img src="../assets/img/Screenshot 2023-12-27 065905.png" width="100%">

# ASP.NET CORE Backend Reference Project "SnackBackend" ('23, #SoftwareEngineering: Backend API)

A full scale .NET project with a focus on clean layering, MVC pattern, authetnication and token handling and all the good stuff that goes into a backend API solution: [clone of the actual study project on GitHub.](https://github.com/heseltime/SnackAdmin-reference-backend-project)

<img src="../assets/img/Screenshot 2023-12-22 230644.png" width="100%" id="backend-endpoints">

Angular frontend project to follow, concluding semester 5 of an intensive [Software Engineering](/rDse) curriculum.

# Der Standard Mock-up ('23, #ArsElectronica/#SoftwareEngineering: Some Experimental Frontend)

See also <a href="/notes">rX Feed</a> and <a href="https://www.derstandard.at/promotion/velcom?DcIYkpda/idsa-eine-universitaet-beginnt#!/" target="_BLANK">the final piece published by Der Standard</a>, a high-end Austrian newspaper (my pretty face is in the header, if you can find me!) -  I delivered the below mockup for a scrollytelling, dynamic version with conveyor belts (the Ars Electronica Festival 2023 took place in an abandoned post (packages) processing plant) but Der Standard went with a simpler static design and layout (their loss!). 

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