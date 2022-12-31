/* 
Copied from https://github.com/derekkedziora/jekyll-demo/blob/master/scripts/mode-switcher.js
https://github.com/derekkedziora/jekyll-demo
Creative Commons Attribution 4.0 International License
edutied by Jack Heseltine, 12/31/2022
*/

let systemInitiatedDark = window.matchMedia("(prefers-color-scheme: dark)"); 
let theme = sessionStorage.getItem('theme');

const iconSun = "/assets/img/sun.svg";
const iconMoon = "/assets/img/moon.svg";

function changeIconImgSrc(src) {
	document.getElementById("theme-toggle-img").src = src;
	document.getElementById("theme-toggle-img--mobile").src = src;
}

function prefersColorTest(systemInitiatedDark) {
if (systemInitiatedDark.matches) {
	document.documentElement.setAttribute('data-theme', 'dark');		
	changeIconImgSrc(iconMoon);
	sessionStorage.setItem('theme', '');
} else {
	document.documentElement.setAttribute('data-theme', 'light');
	changeIconImgSrc(iconSun);
	sessionStorage.setItem('theme', '');
}
}

function modeSwitcher() {
	let theme = sessionStorage.getItem('theme');
	if (theme === "dark") {
		document.documentElement.setAttribute('data-theme', 'light');
		sessionStorage.setItem('theme', 'light');
		changeIconImgSrc(iconSun);
	}	else if (theme === "light") {
		document.documentElement.setAttribute('data-theme', 'dark');
		sessionStorage.setItem('theme', 'dark');
		changeIconImgSrc(iconMoon);
	} else if (systemInitiatedDark.matches) {	
		document.documentElement.setAttribute('data-theme', 'light');
		sessionStorage.setItem('theme', 'light');
		changeIconImgSrc(iconSun);
	} else {
		document.documentElement.setAttribute('data-theme', 'dark');
		sessionStorage.setItem('theme', 'dark');
		changeIconImgSrc(iconMoon);
	}
}

document.addEventListener("DOMContentLoaded", function(event) {
	if (systemInitiatedDark.matches) {
		changeIconImgSrc(iconMoon);
	} else {
		changeIconImgSrc(iconSun);
	}

	systemInitiatedDark.addListener(prefersColorTest);

	if (theme === "dark") {
		document.documentElement.setAttribute('data-theme', 'dark');
		sessionStorage.setItem('theme', 'dark');
		changeIconImgSrc(iconMoon);
	} else if (theme === "light") {
		document.documentElement.setAttribute('data-theme', 'light');
		sessionStorage.setItem('theme', 'light');
		changeIconImgSrc(iconSun);
	}
});