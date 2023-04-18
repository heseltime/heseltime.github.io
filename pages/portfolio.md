---
layout: Post
permalink: /portfolio
title: Portfolio
feedformat: none
---

On top of DevOps I do Software Engineering work from formal training in the subject, with multi-year experience in Enterprise Content Management (ECM) and tangential implementations like Single Page Applications (SPAs), sprinkled in there.

# ECM: D.velop Documents/Process (2020-23)

D.velop is a German company marketing a mid-tier ECM system that is now very common in the DACH region. It is often named in the innovative categories in Gartner Magic Quadrant because it is a well thought out system that nevertheless makes due with some legacy code and languages especially in their Workflow component (Flow Designer). The latter is being revamped though, as D.velop Process, on top of a Camunda Workflow Engine. Camunda itself is an (Alfresco) Activiti Fork.

This work took place for the Red Cross and is mostly confidential as such. I can share the following aspects of a three-year, multi-project engagement 2020-23.

## Projects

- The work was multi-departmental, from planning over modelling (BPMN) to execution with two external partners. I lead the internal code implementation: languges used were Java, Groovy, JavaScript, JPL (proprietary).
- The work had one important archiving component, using a third party tool that protects records (revision safe archiving, the tool is [Graudata](https://www.graudata.com)) and makes them conform to the hefty regularity requirements in the blood banking field.
- Most of the work was about expanding workflow-capability, i.e. automisation, in the documents arena, where documentation is a central aspect of blood banking. The most complicated workflow was a five-part (!) cycle including blood bank worker training, archiving of trainable documents, clear distinction of documents that are being worked on and documents that are valid and need to be known and documented as trained to all the relevant professionals, lab workers and doctors mainly, in the different departments. It also included a multi-stage signing step (for department heads/experts) to  guarantee validity of the documents that are being circulated in the blood bank and meet Austrian/EU regularity requirements of these documents: this gives an idea of the nature of the ECM approach and the topics in ECM in companies that are not typically thought of as "content companies," here in health and blood banking particularly. 
- The work saw a team expansion by a factor of three, all working on ECM in Linz blood bank. The ECM-commitment of the blood bank grew to hotline/support implementation dedicated to ECM, and internal trainings focussed around ECM. 
- The end of my tenure with the Red Cross saw the inception of the study project documented in the rX-section of this website: The goal of the project is to establish modern internal development workflows independent of external consultants and contractors to advance the quantity and quality of internal initiatives. I continue to stay involved on a volunteer basis and through this study project.

I owned all of the above initiatives in the capacity of a DevOps Engineer focussed on internal Softare Implementation.

# SPA: co2work (2022)

[co2work](http://co2work.at) is an Upper Austrian co-working place lander with C02-Footprint calculator for social media sharing. 

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