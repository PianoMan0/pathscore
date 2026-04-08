const startBtn = document.getElementById("startBtn");
const stopBtn = document.getElementById("stopBtn");
const gpsStatusEl = document.getElementById("gpsStatus");
const stepCountEl = document.getElementById("stepCount");
const tempoDisplayEl = document.getElementById("tempoDisplay");
const noteDisplayEl = document.getElementById("noteDisplay");
const accuracyEl = document.getElementById("accuracy");
const distanceEl = document.getElementById("distance");
const canvas = document.getElementById("mapCanvas");
const ctx = canvas ? canvas.getContext("2d") : null;
const downloadBtn = document.getElementById("downloadBtn");
const keyDisplayEl = document.getElementById("keyDisplay");
const historyBtn = document.getElementById("historyBtn");
const historyPanel = document.getElementById("historyPanel");
const closeHistoryBtn = document.getElementById("closeHistory");
const walksList = document.getElementById("walksList");
const clearHistoryBtn = document.getElementById("clearHistoryBtn");

function setupHighDPICanvas() {
  if (!canvas || !ctx) return;
  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.getBoundingClientRect();
  canvas.width = rect.width * dpr;
  canvas.height = rect.height * dpr;
  canvas.style.width = rect.width + 'px';
  canvas.style.height = rect.height + 'px';
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.scale(dpr, dpr);
}

try {
  setupHighDPICanvas();
} catch (e) {
  console.warn("High DPI setup failed, using default canvas");
}

const appState = {
  audioCtx: null,
  watchId: null,
  positions: [],
  lastRawPoint: null,
  distanceAccumulator: 0,
  baseAngle: null,
  currentTempo: 90,
  stepCooldown: 0,
  isWalking: false,
  walkStartTime: null,
  totalDistance: 0,
  gpsRetries: 0,
  lastAccuracy: null,
  audioNodes: {},
  ambientTimer: null,
  motionEngine: null,
  lowMotionCounter: 0,
  lastMotionTime: null,
  lastNoteTime: 0,
  noteSeed: 0,
  chordProgression: [0, 4, 5, 3],
  progressionStep: 0,
  songStep: 0,
  mode: "major",
  root: 60,
  scalePattern: [0, 2, 4, 5, 7, 9, 11],
  keyName: "C",
  recordedChunks: [],
  recordingBlob: null,
  mediaRecorder: null,
  masterGain: null
};

const NOTE_DISTANCE = 3;
const NOTE_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
const PAD_VOLUME = 0.15;
const GPS_TIMEOUT = 15000; // 15 seconds
const GPS_MAX_RETRIES = 3;
const ACCURACY_THRESHOLD = 50;
const MIN_DISTANCE_FILTER = 0.5; // meters - minimum movement to register
const AMBIENT_INTERVAL = 5500;
const LOW_MOTION_NOTE_INTERVAL = 2200;
const MIN_NOTE_INTERVAL = 1500;
const STEP_THRESHOLD = 10.8;
const STEP_COOLDOWN = 5;
const MAX_TEMPO_SPEED = 2.2;
const LOW_SPEED_THRESHOLD = 0.12;

const MODE_PATTERNS = {
  major: [0, 2, 4, 5, 7, 9, 11],
  minor: [0, 2, 3, 5, 7, 8, 10]
};

const KEY_ROOTS = [60, 62, 64, 65, 67, 69];

const PROGRESSIONS = {
  major: [
    [0, 4, 5, 3],
    [0, 5, 3, 4],
    [0, 4, 1, 5],
    [0, 3, 5, 4],
    [0, 2, 5, 4]
  ],
  minor: [
    [0, 5, 3, 7],
    [0, 3, 4, 5],
    [0, 6, 4, 7],
    [0, 5, 2, 3]
  ]
};

const MELODY_MOTION_MULTIPLIER = 2;

// Utility Functions
const toRad = (d) => (d * Math.PI) / 180;

function distance(a, b) {
  const R = 6371000;
  const dLat = toRad(b.lat - a.lat);
  const dLon = toRad(b.lon - a.lon);
  const lat1 = toRad(a.lat);
  const lat2 = toRad(b.lat);

  const h =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLon / 2) ** 2;

  return R * 2 * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
}

function bearing(a, b) {
  const lat1 = toRad(a.lat);
  const lat2 = toRad(b.lat);
  const dLon = toRad(b.lon - a.lon);

  const y = Math.sin(dLon) * Math.cos(lat2);
  const x =
    Math.cos(lat1) * Math.sin(lat2) -
    Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLon);

  return Math.atan2(y, x);
}

function smooth(prev, next, f = 0.15) {
  return {
    lat: prev.lat + (next.lat - prev.lat) * f,
    lon: prev.lon + (next.lon - prev.lon) * f,
    t: next.t
  };
}

function midiToFreq(m) {
  return 440 * Math.pow(2, (m - 69) / 12);
}

function formatTime(ms) {
  const seconds = Math.floor(ms / 1000);
  const minutes = Math.floor(seconds / 60);
  const secs = seconds % 60;
  return `${minutes}:${secs.toString().padStart(2, '0')}`;
}

function formatDistance(meters) {
  if (meters < 1000) return `${Math.round(meters)}m`;
  return `${(meters / 1000).toFixed(2)}km`;
}

function clamp(value, min, max) {
  return Math.min(Math.max(value, min), max);
}

function getMidiName(midi) {
  const note = NOTE_NAMES[((midi % 12) + 12) % 12];
  const octave = Math.floor(midi / 12) - 1;
  return `${note}${octave}`;
}

function scaleDegreeToMidi(degree) {
  const octave = Math.floor(degree / appState.scalePattern.length);
  const index = ((degree % appState.scalePattern.length) + appState.scalePattern.length) % appState.scalePattern.length;
  return appState.root + appState.scalePattern[index] + octave * 12;
}

function getChordNotes(degree) {
  return [
    scaleDegreeToMidi(degree),
    scaleDegreeToMidi(degree + 2),
    scaleDegreeToMidi(degree + 4)
  ];
}

function getProgressionChord() {
  return appState.chordProgression[appState.progressionStep % appState.chordProgression.length];
}

function advanceProgression() {
  appState.progressionStep = (appState.progressionStep + 1) % appState.chordProgression.length;
}

function shouldPlayAmbientNote() {
  if (!appState.isWalking) return false;
  const idleTime = Date.now() - appState.lastMotionTime;
  return idleTime >= AMBIENT_INTERVAL;
}

function connectOutput(node) {
  if (!appState.audioCtx) return;
  if (appState.masterGain) {
    node.connect(appState.masterGain);
  } else {
    node.connect(appState.audioCtx.destination);
  }
}

function createMediaRecorder(stream) {
  if (!window.MediaRecorder) return null;

  try {
    const recorder = new MediaRecorder(stream);
    recorder.ondataavailable = (event) => {
      if (event.data && event.data.size > 0) {
        appState.recordedChunks.push(event.data);
      }
    };

    recorder.onstop = () => {
      if (appState.recordedChunks.length > 0) {
        appState.recordingBlob = new Blob(appState.recordedChunks, { type: recorder.mimeType || "audio/webm" });
        if (downloadBtn) downloadBtn.disabled = false;
        gpsStatusEl.textContent = "Song ready to download";
      }
    };

    return recorder;
  } catch (e) {
    console.warn("MediaRecorder creation failed:", e);
    return null;
  }
}

function startMotionEngine() {
  stopMotionEngine();
  appState.motionEngine = window.setInterval(() => {
    if (!appState.isWalking || !appState.audioCtx) return;
    const idle = Date.now() - appState.lastNoteTime;
    if (idle < LOW_MOTION_NOTE_INTERVAL * 0.6) return;

    const chordDegree = getProgressionChord();
    const chordNotes = getChordNotes(chordDegree);
    playChordNotes(chordNotes, 1.6, 0.18);
    playHat(0.68);
    playKick(0.9);

    if (Math.random() > 0.5) {
      const leadNote = scaleDegreeToMidi(chordDegree + 2) + 12;
      playMelody(leadNote, 0.58, 0.18);
      playHat(0.4);
    }

    if (noteDisplayEl) noteDisplayEl.textContent = getMidiName(chordNotes[0]);
    appState.lastNoteTime = Date.now();
  }, 540);
}

function stopMotionEngine() {
  if (appState.motionEngine) {
    clearInterval(appState.motionEngine);
    appState.motionEngine = null;
  }
}

function initAudio() {
  if (appState.audioCtx) return;

  try {
    appState.audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    appState.masterGain = appState.audioCtx.createGain();
    appState.masterGain.gain.value = 0.9;
    appState.masterGain.connect(appState.audioCtx.destination);

    const recordDestination = appState.audioCtx.createMediaStreamDestination();
    appState.masterGain.connect(recordDestination);
    appState.mediaRecorder = createMediaRecorder(recordDestination.stream);

    const padOsc1 = appState.audioCtx.createOscillator();
    const padOsc2 = appState.audioCtx.createOscillator();
    const padFilter = appState.audioCtx.createBiquadFilter();
    const padGain = appState.audioCtx.createGain();

    padOsc1.type = "sine";
    padOsc2.type = "sine";
    padOsc1.frequency.value = midiToFreq(48);
    padOsc2.frequency.value = midiToFreq(55);

    padFilter.type = "lowpass";
    padFilter.frequency.value = 800;

    padGain.gain.value = PAD_VOLUME;

    padOsc1.connect(padFilter);
    padOsc2.connect(padFilter);
    padFilter.connect(padGain);
    connectOutput(padGain);

    padOsc1.start();
    padOsc2.start();

    appState.audioNodes = { padOsc1, padOsc2, padFilter, padGain };
  } catch (e) {
    console.error("Audio init failed:", e);
  }
}

function updateAmbientPad(speed) {
  if (!appState.audioCtx || !appState.audioNodes.padFilter || !appState.audioNodes.padGain) return;

  const targetFreq = clamp(600 + speed * 900, 600, 1400);
  appState.audioNodes.padFilter.frequency.setTargetAtTime(targetFreq, appState.audioCtx.currentTime, 0.8);

  const targetGain = clamp(PAD_VOLUME + speed * 0.05, PAD_VOLUME, 0.25);
  appState.audioNodes.padGain.gain.setTargetAtTime(targetGain, appState.audioCtx.currentTime, 1.2);
}

function playMelody(midi, duration = 0.5, velocity = 0.35) {
  if (!appState.audioCtx) return;

  try {
    const now = appState.audioCtx.currentTime;
    const filter = appState.audioCtx.createBiquadFilter();
    const gain = appState.audioCtx.createGain();

    filter.type = "lowpass";
    filter.frequency.value = 1000 + Math.random() * 900;
    filter.Q.value = 1.3;

    gain.gain.setValueAtTime(0, now);
    gain.gain.linearRampToValueAtTime(velocity, now + 0.02);
    gain.gain.exponentialRampToValueAtTime(0.001, now + duration);

    const voices = [
      { type: "triangle", note: midi, mix: 1 },
      { type: "sine", note: midi - 12, mix: 0.24 },
      { type: "triangle", note: midi + 7, mix: 0.18 }
    ];

    voices.forEach(({ type, note, mix }) => {
      const osc = appState.audioCtx.createOscillator();
      const voiceGain = appState.audioCtx.createGain();
      osc.type = type;
      osc.frequency.value = midiToFreq(note);
      voiceGain.gain.setValueAtTime(velocity * mix, now);
      osc.connect(voiceGain);
      voiceGain.connect(filter);
      osc.start(now);
      osc.stop(now + duration);
    });

    filter.connect(gain);
    connectOutput(gain);
  } catch (e) {
    console.warn("Melody playback failed:", e);
  }
}

function playChordNotes(notes, duration = 1.4, velocity = 0.16) {
  if (!appState.audioCtx) return;

  try {
    const now = appState.audioCtx.currentTime;
    const filter = appState.audioCtx.createBiquadFilter();
    const gain = appState.audioCtx.createGain();

    filter.type = "lowpass";
    filter.frequency.value = 1000 + Math.random() * 330;
    filter.Q.value = 1.05;

    gain.gain.setValueAtTime(0, now);
    gain.gain.linearRampToValueAtTime(velocity, now + 0.08);
    gain.gain.exponentialRampToValueAtTime(0.001, now + duration);

    notes.forEach(note => {
      const osc = appState.audioCtx.createOscillator();
      const voiceGain = appState.audioCtx.createGain();
      osc.type = "triangle";
      osc.frequency.value = midiToFreq(note);
      voiceGain.gain.setValueAtTime(velocity * 0.9, now);
      osc.connect(voiceGain);
      voiceGain.connect(filter);
      osc.start(now);
      osc.stop(now + duration);
    });

    filter.connect(gain);
    connectOutput(gain);
  } catch (e) {
    console.warn("Chord playback failed:", e);
  }
}

function playAmbientNote() {
  const chordDegree = getProgressionChord();
  const notes = getChordNotes(chordDegree);
  playChordNotes(notes, 1.8, 0.18);
  if (noteDisplayEl) noteDisplayEl.textContent = getMidiName(notes[0]);
}

function startAmbientEngine() {
  stopAmbientEngine();
  appState.ambientTimer = window.setInterval(() => {
    if (shouldPlayAmbientNote()) {
      playAmbientNote();
      appState.lastMotionTime = Date.now();
    }
  }, AMBIENT_INTERVAL);
}

function stopAmbientEngine() {
  if (appState.ambientTimer) {
    clearInterval(appState.ambientTimer);
    appState.ambientTimer = null;
  }
}

function playKick(intensity = 1, when) {
  if (!appState.audioCtx) return;
  const now = when || appState.audioCtx.currentTime;
  const osc = appState.audioCtx.createOscillator();
  const gain = appState.audioCtx.createGain();

  osc.type = "sine";
  osc.frequency.setValueAtTime(120, now);
  osc.frequency.exponentialRampToValueAtTime(45, now + 0.18);

  gain.gain.setValueAtTime(0.26 * intensity, now);
  gain.gain.exponentialRampToValueAtTime(0.001, now + 0.25);

  osc.connect(gain);
  connectOutput(gain);

  osc.start(now);
  osc.stop(now + 0.26);
}

function playHat(intensity = 0.7, when) {
  if (!appState.audioCtx) return;
  const now = when || appState.audioCtx.currentTime;
  const source = appState.audioCtx.createBufferSource();
  const buffer = appState.audioCtx.createBuffer(1, appState.audioCtx.sampleRate * 0.05, appState.audioCtx.sampleRate);
  const data = buffer.getChannelData(0);

  for (let i = 0; i < data.length; i++) {
    data[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / data.length, 2);
  }

  source.buffer = buffer;
  const hp = appState.audioCtx.createBiquadFilter();
  hp.type = "highpass";
  hp.frequency.value = 4200;

  const gain = appState.audioCtx.createGain();
  gain.gain.setValueAtTime(0.08 * intensity, now);
  gain.gain.exponentialRampToValueAtTime(0.001, now + 0.06);

  source.connect(hp);
  hp.connect(gain);
  connectOutput(gain);

  source.start(now);
  source.stop(now + 0.07);
}

function playSnare(intensity = 0.95, when) {
  if (!appState.audioCtx) return;
  const now = when || appState.audioCtx.currentTime;
  const source = appState.audioCtx.createBufferSource();
  const buffer = appState.audioCtx.createBuffer(1, appState.audioCtx.sampleRate * 0.09, appState.audioCtx.sampleRate);
  const data = buffer.getChannelData(0);

  for (let i = 0; i < data.length; i++) {
    data[i] = (Math.random() * 2 - 1) * (1 - i / data.length);
  }

  source.buffer = buffer;
  const band = appState.audioCtx.createBiquadFilter();
  band.type = "bandpass";
  band.frequency.value = 1800;
  band.Q.value = 0.8;

  const gain = appState.audioCtx.createGain();
  gain.gain.setValueAtTime(0.18 * intensity, now);
  gain.gain.exponentialRampToValueAtTime(0.002, now + 0.12);

  source.connect(band);
  band.connect(gain);
  connectOutput(gain);

  source.start(now);
  source.stop(now + 0.11);
}

function playPercussion(force = 1) {
  if (!appState.audioCtx) return;

  try {
    const intensity = clamp(force, 0.9, 1.8);
    const now = appState.audioCtx.currentTime;
    playKick(intensity, now);
    playHat(intensity * 0.6, now + 0.06);
    if (Math.random() > 0.25) {
      playSnare(intensity * 0.85, now + 0.18);
    }
    if (Math.random() > 0.55) {
      playHat(intensity * 0.5, now + 0.12);
    }
  } catch (e) {
    console.warn("Percussion playback failed:", e);
  }
}

window.addEventListener("devicemotion", e => {
  if (!appState.isWalking || !e.accelerationIncludingGravity) return;

  const a = e.accelerationIncludingGravity;
  const mag = Math.sqrt(a.x * a.x + a.y * a.y + a.z * a.z);

  if (mag > STEP_THRESHOLD && appState.stepCooldown <= 0) {
    appState.stepCooldown = STEP_COOLDOWN;
    stepCountEl.textContent = Number(stepCountEl.textContent) + 1;
    playPercussion(1.1);
    playHat(0.5);
    if (Math.random() > 0.6) {
      playSnare(0.65);
    }
  }

  if (appState.stepCooldown > 0) appState.stepCooldown--;
});

function handlePosition(pos) {
  if (!appState.isWalking) return;

  appState.gpsRetries = 0;
  
  const raw = {
    lat: pos.coords.latitude,
    lon: pos.coords.longitude,
    t: pos.timestamp,
    accuracy: pos.coords.accuracy
  };

  appState.lastAccuracy = pos.coords.accuracy;
  updateAccuracyDisplay(pos.coords.accuracy);

  appState.lastMotionTime = Date.now();

  if (!appState.lastRawPoint) {
    appState.lastRawPoint = raw;
    appState.positions.push(raw);
    drawPath();
    gpsStatusEl.textContent = "Acquiring...";
    return;
  }

  const smoothed = smooth(appState.lastRawPoint, raw);
  appState.lastRawPoint = raw;

  const prev = appState.positions[appState.positions.length - 1];
  const dist = distance(prev, smoothed);

  if (dist < MIN_DISTANCE_FILTER) {
    appState.distanceAccumulator += MIN_DISTANCE_FILTER * 0.35;
    updateDistanceDisplay(appState.totalDistance);
    drawPath();
    gpsStatusEl.textContent = "Stationary — ambient music";
    processMovement(prev, smoothed, dist);
    return;
  }

  appState.positions.push(smoothed);
  appState.totalDistance += dist;
  updateDistanceDisplay(appState.totalDistance);
  drawPath();

  gpsStatusEl.textContent = "Tracking";
  processMovement(prev, smoothed, dist);
}

function handleGPSError(err) {
  console.warn("GPS Error:", err);
  
  if (appState.gpsRetries < GPS_MAX_RETRIES) {
    appState.gpsRetries++;
    gpsStatusEl.textContent = `Retrying GPS... (${appState.gpsRetries}/${GPS_MAX_RETRIES})`;
  } else {
    gpsStatusEl.textContent = `GPS Error: ${err.message}. Check permissions & accuracy.`;
  }
}

function processMovement(prev, point, dist) {
  appState.distanceAccumulator += dist;
  appState.lowMotionCounter = appState.lowMotionCounter || 0;

  const dt = Math.max((point.t - prev.t) / 1000, 0.01);
  const speed = dist / dt;

  updateAmbientPad(speed);
  appState.currentTempo = Math.round(75 + Math.min(speed, MAX_TEMPO_SPEED) * 50);
  tempoDisplayEl.textContent = `${appState.currentTempo} BPM`;

  const angle = bearing(prev, point);
  if (appState.baseAngle === null) appState.baseAngle = angle;

  const diff = angle - appState.baseAngle;
  appState.baseAngle += diff * 0.1;

  const idleTime = Date.now() - appState.lastNoteTime;
  const shouldPlayNote =
    appState.distanceAccumulator >= NOTE_DISTANCE ||
    speed <= LOW_SPEED_THRESHOLD ||
    idleTime >= LOW_MOTION_NOTE_INTERVAL;

  if (shouldPlayNote) {
    appState.distanceAccumulator = 0;

    const chordDegree = getProgressionChord();
    if (appState.songStep % 4 === 0) {
      const chordNotes = getChordNotes(chordDegree);
      playChordNotes(chordNotes, 1.4, clamp(0.14 + speed * 0.08, 0.14, 0.22));
    }

    const melodyDegree = chordDegree + (appState.songStep * MELODY_MOTION_MULTIPLIER);
    const note = scaleDegreeToMidi(melodyDegree) + (speed > 0.25 ? 12 : 0);
    const velocity = clamp(0.28 + speed * 0.28, 0.28, 0.62);
    const duration = speed <= LOW_SPEED_THRESHOLD ? 0.82 : 0.52;

    playMelody(note, duration, velocity);
    playHat(0.58);

    if (speed > 0.12) {
      playMelody(note + 4, duration * 0.72, velocity * 0.18);
    }
    if (speed > 0.45) {
      playMelody(note + 7, duration * 0.48, velocity * 0.12);
      playSnare(0.92);
    }

    playPercussion(clamp(1 + speed * 0.4, 1, 1.6));
    appState.songStep += 1;

    if (appState.songStep % 4 === 0) {
      advanceProgression();
    }

    if (noteDisplayEl) noteDisplayEl.textContent = getMidiName(note);
    appState.lastNoteTime = Date.now();

    if (speed <= LOW_SPEED_THRESHOLD || dist < MIN_DISTANCE_FILTER) {
      appState.lowMotionCounter++;
      if (appState.lowMotionCounter > 2) {
        playAmbientNote();
      }
    } else {
      appState.lowMotionCounter = 0;
    }
  }
}

function updateAccuracyDisplay(accuracy) {
  if (accuracyEl) {
    accuracyEl.textContent = accuracy ? `${Math.round(accuracy)}m` : "Unknown";
  }
}

function updateDistanceDisplay(distance) {
  if (distanceEl) {
    distanceEl.textContent = formatDistance(distance);
  }
}

function drawPath() {
  if (!canvas || !ctx) return;
  const dpr = window.devicePixelRatio || 1;
  const width = canvas.width / dpr;
  const height = canvas.height / dpr;
  ctx.clearRect(0, 0, width, height);
  if (appState.positions.length < 2) return;

  const padding = 20;
  const xs = appState.positions.map(p => p.lon);
  const ys = appState.positions.map(p => p.lat);

  const minX = Math.min(...xs);
  const maxX = Math.max(...xs);
  const minY = Math.min(...ys);
  const maxY = Math.max(...ys);

  const spanX = maxX - minX || 0.00001;
  const spanY = maxY - minY || 0.00001;

  const scale = Math.min(
    (width - padding * 2) / spanX,
    (height - padding * 2) / spanY
  );

  const project = p => ({
    x: padding + (p.lon - minX) * scale,
    y: height - (padding + (p.lat - minY) * scale)
  });

  ctx.lineWidth = 3;
  ctx.strokeStyle = "#38bdf8";
  ctx.beginPath();

  appState.positions.forEach((p, i) => {
    const { x, y } = project(p);
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  });

  ctx.stroke();
}

function saveWalk() {
  if (appState.positions.length < 2) return null;

  const walk = {
    id: Date.now(),
    timestamp: new Date().toLocaleString(),
    distance: appState.totalDistance,
    steps: Number(stepCountEl.textContent),
    points: appState.positions.length,
    tempoAvg: appState.currentTempo,
    positions: appState.positions
  };

  const walks = JSON.parse(localStorage.getItem("pathscoreWalks") || "[]");
  walks.push(walk);
  localStorage.setItem("pathscoreWalks", JSON.stringify(walks));

  return walk;
}

function loadWalks() {
  return JSON.parse(localStorage.getItem("pathscoreWalks") || "[]");
}

function displayWalkHistory() {
  const walks = loadWalks();
  walksList.innerHTML = "";

  if (walks.length === 0) {
    walksList.innerHTML = "<p style='text-align:center;color:#999;'>No walks yet. Start your first walk!</p>";
    return;
  }

  walks.slice().reverse().forEach(walk => {
    const item = document.createElement("div");
    item.className = "walk-item";
    item.innerHTML = `
      <div class="walk-info">
        <h4>${walk.timestamp}</h4>
        <p>Distance: ${formatDistance(walk.distance)}</p>
        <p>Steps: ${walk.steps} | Points: ${walk.points}</p>
      </div>
      <button class="replay-btn" onclick="replayWalk(${walk.id})">Replay</button>
    `;
    walksList.appendChild(item);
  });
}

function replayWalk(walkId) {
  const walks = loadWalks();
  const walk = walks.find(w => w.id === walkId);
  if (!walk) return;

  historyPanel.style.display = "none";
  appState.positions = walk.positions;
  appState.totalDistance = walk.distance;
  drawPath();

  alert(`Replaying: ${walk.timestamp}\nDistance: ${formatDistance(walk.distance)}\nSteps: ${walk.steps}`);
}

function startWalk() {
  if (!navigator.geolocation) {
    gpsStatusEl.textContent = "Geolocation not available";
    return;
  }

  initAudio();

  appState.positions = [];
  appState.lastRawPoint = null;
  appState.distanceAccumulator = 0;
  appState.baseAngle = null;
  appState.totalDistance = 0;
  appState.isWalking = true;
  appState.walkStartTime = Date.now();
  appState.gpsRetries = 0;
  appState.lowMotionCounter = 0;
  appState.lastMotionTime = Date.now();
  appState.lastNoteTime = Date.now();
  appState.noteSeed = 0;
  appState.mode = Math.random() > 0.35 ? "major" : "minor";
  appState.root = KEY_ROOTS[Math.floor(Math.random() * KEY_ROOTS.length)];
  appState.scalePattern = MODE_PATTERNS[appState.mode];
  appState.keyName = `${NOTE_NAMES[appState.root % 12]}${appState.mode === "minor" ? "m" : ""}`;
  appState.chordProgression = PROGRESSIONS[appState.mode][Math.floor(Math.random() * PROGRESSIONS[appState.mode].length)].slice();
  appState.progressionStep = 0;
  appState.songStep = 0;
  appState.recordedChunks = [];
  appState.recordingBlob = null;

  if (appState.audioNodes.padOsc1 && appState.audioNodes.padOsc2 && appState.audioNodes.padGain) {
    appState.audioNodes.padOsc1.frequency.value = midiToFreq(appState.root - 12);
    appState.audioNodes.padOsc2.frequency.value = midiToFreq(appState.root - 5);
    appState.audioNodes.padGain.gain.value = PAD_VOLUME;
  }

  stepCountEl.textContent = "0";
  tempoDisplayEl.textContent = "-- BPM";
  noteDisplayEl.textContent = "--";
  if (keyDisplayEl) keyDisplayEl.textContent = appState.keyName;
  if (downloadBtn) downloadBtn.disabled = true;
  updateAccuracyDisplay(null);
  updateDistanceDisplay(0);

  gpsStatusEl.textContent = "Requesting GPS…";

  appState.watchId = navigator.geolocation.watchPosition(
    handlePosition,
    handleGPSError,
    {
      enableHighAccuracy: true,
      maximumAge: 0,
      timeout: GPS_TIMEOUT
    }
  );

  startAmbientEngine();
  startMotionEngine();
  if (appState.mediaRecorder && appState.mediaRecorder.state === "inactive") {
    appState.recordedChunks = [];
    appState.mediaRecorder.start();
    gpsStatusEl.textContent = "Recording song...";
  }
  startBtn.disabled = true;
  stopBtn.disabled = false;
}

function stopWalk() {
  appState.isWalking = false;

  if (appState.watchId) {
    navigator.geolocation.clearWatch(appState.watchId);
    appState.watchId = null;
  }

  stopAmbientEngine();
  stopMotionEngine();
  if (appState.audioNodes.padGain) {
    appState.audioNodes.padGain.gain.value = 0;
  }
  if (appState.mediaRecorder && appState.mediaRecorder.state === "recording") {
    appState.mediaRecorder.stop();
  }

  const walk = saveWalk();
  if (walk) {
    gpsStatusEl.textContent = "Walk saved! Tap history to relive it.";
  } else {
    gpsStatusEl.textContent = "Stopped";
  }

  startBtn.disabled = false;
  stopBtn.disabled = true;
}

startBtn.addEventListener("click", async () => {
  initAudio();
  if (appState.audioCtx && appState.audioCtx.state === "suspended") {
    await appState.audioCtx.resume();
  }
  startWalk();
});

stopBtn.addEventListener("click", stopWalk);

downloadBtn?.addEventListener("click", () => {
  if (!appState.recordingBlob) return;
  const url = URL.createObjectURL(appState.recordingBlob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `pathscore-song-${Date.now()}.webm`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 2000);
});

historyBtn.addEventListener("click", () => {
  historyPanel.style.display = historyPanel.style.display === "none" ? "block" : "none";
  if (historyPanel.style.display === "block") {
    displayWalkHistory();
  }
});

closeHistoryBtn.addEventListener("click", () => {
  historyPanel.style.display = "none";
});

clearHistoryBtn.addEventListener("click", () => {
  if (confirm("Delete all walk history?")) {
    localStorage.removeItem("pathscoreWalks");
    displayWalkHistory();
  }
});

window.addEventListener("resize", () => {
  if (canvas && ctx) {
    setupHighDPICanvas();
    drawPath();
  }
});

[startBtn, stopBtn, gpsStatusEl, stepCountEl, tempoDisplayEl, noteDisplayEl, keyDisplayEl, downloadBtn, historyBtn, historyPanel, closeHistoryBtn, walksList, clearHistoryBtn].forEach(el => {
  if (!el) {
    console.error("DOM element missing - check HTML structure");
  }
});

if (loadWalks().length > 0) {
} else {
  // First time user - show welcome message
  gpsStatusEl.textContent = "Ready";
}

console.log("🎵 Pathscore initialized successfully");
console.log("GPS Timeout: " + GPS_TIMEOUT + "ms | Max Retries: " + GPS_MAX_RETRIES);
console.log("Min Distance: " + MIN_DISTANCE_FILTER + "m | Note Distance: " + NOTE_DISTANCE + "m");
