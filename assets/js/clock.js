const hr = document.getElementById("hr");
const min = document.getElementById("min");
const sec = document.getElementById("sec");

const rotation = (target, val) => {
  target.style.transform = `rotate(${val}deg)`;
};

const viennaFormatter = new Intl.DateTimeFormat("en-GB", {
  timeZone: "Europe/Vienna",
  hour: "numeric",
  minute: "numeric",
  second: "numeric",
  hour12: false
});

const clock = () => {
  const parts = viennaFormatter.formatToParts(new Date());

  const hh = Number(parts.find(p => p.type === "hour").value);
  const mm = Number(parts.find(p => p.type === "minute").value);
  const ss = Number(parts.find(p => p.type === "second").value);

  const hourDeg = ((hh % 12) + mm / 60) * 30;
  const minDeg = mm * 6;
  const secDeg = ss * 6;

  rotation(hr, hourDeg);
  rotation(min, minDeg);
  rotation(sec, secDeg);

  setTimeout(clock, 500);
};

window.onload = clock;
