// Taylor Series Visualizer - Main JavaScript

// Global state
let currentFunction = 'sin(x)';
let centerPoint = 0;
let numTerms = 5;
let viewRange = 10;
let animationInterval = null;
let currentLatex = '';
let katexReady = false;

// Animation settings
let animationSettings = {
    enabled: true,
    speed: 350,
    transitionDuration: 200,
    easing: 'cubic-in-out'
};

// Wait for KaTeX to load
function waitForKatex() {
    return new Promise((resolve) => {
        if (typeof katex !== 'undefined') {
            resolve();
        } else {
            const checkInterval = setInterval(() => {
                if (typeof katex !== 'undefined') {
                    clearInterval(checkInterval);
                    resolve();
                }
            }, 50);
        }
    });
}

// DOM elements
let elements = {};

function initDOMElements() {
    elements = {
        exampleSelect: document.getElementById('example-select'),
        functionInput: document.getElementById('function-input'),
        centerSlider: document.getElementById('center-slider'),
        centerValue: document.getElementById('center-value'),
        termsSlider: document.getElementById('terms-slider'),
        termsValue: document.getElementById('terms-value'),
        rangeSlider: document.getElementById('range-slider'),
        rangeValue: document.getElementById('range-value'),
        latexGeneral: document.getElementById('latex-general'),
        latexExpanded: document.getElementById('latex-expanded'),
        latexRaw: document.getElementById('latex-raw'),
        errorMessage: document.getElementById('error-message'),
        animateBtn: document.getElementById('animate-btn'),
        resetBtn: document.getElementById('reset-btn'),
        errorToggle: document.getElementById('error-toggle'),
        errorContainer: document.getElementById('error-container'),
        copyLatexBtn: document.getElementById('copy-latex-btn'),
        toast: document.getElementById('toast'),
        sliderSettingsToggle: document.getElementById('slider-settings-toggle'),
        sliderSettingsContent: document.getElementById('slider-settings-content'),
        animationSettingsToggle: document.getElementById('animation-settings-toggle'),
        animationSettingsContent: document.getElementById('animation-settings-content'),
        enableAnimations: document.getElementById('enable-animations'),
        animationSpeedSelect: document.getElementById('animation-speed'),
        transitionDuration: document.getElementById('transition-duration'),
        transitionValueDisplay: document.getElementById('transition-value'),
        easingFunction: document.getElementById('easing-function'),
        centerMin: document.getElementById('center-min'),
        centerMax: document.getElementById('center-max'),
        centerStep: document.getElementById('center-step'),
        termsMin: document.getElementById('terms-min'),
        termsMax: document.getElementById('terms-max'),
        termsStep: document.getElementById('terms-step'),
        rangeMin: document.getElementById('range-min'),
        rangeMax: document.getElementById('range-max'),
        rangeStep: document.getElementById('range-step')
    };
}

// Factorial with memoization
const factorialCache = [1, 1];
function factorial(n) {
    if (n < 0) return 1;
    if (n < factorialCache.length) return factorialCache[n];
    let result = factorialCache[factorialCache.length - 1];
    for (let i = factorialCache.length; i <= n; i++) {
        result *= i;
        factorialCache[i] = result;
    }
    return result;
}

// Binomial coefficient
function binomial(n, k) {
    if (k < 0 || k > n) return 0;
    if (k === 0 || k === n) return 1;
    return factorial(n) / (factorial(k) * factorial(n - k));
}

// Compute nth derivative using finite difference with proper coefficients
// Uses the central difference formula with optimal step size
function numericalDerivative(f, x, n) {
    if (n === 0) return f(x);

    // Optimal step size for nth derivative: h ~ eps^(1/(n+2)) where eps ~ 1e-16
    // For practical purposes, we use a formula that balances truncation and roundoff error
    const eps = 2.2e-16;
    const h = Math.pow(eps, 1 / (n + 2)) * Math.max(1, Math.abs(x));

    // Central difference formula: f^(n)(x) ≈ (1/h^n) * Σ_{k=0}^{n} (-1)^k * C(n,k) * f(x + (n/2 - k)*h)
    let sum = 0;
    for (let k = 0; k <= n; k++) {
        const coeff = Math.pow(-1, k) * binomial(n, k);
        const xk = x + (n / 2 - k) * h;
        const fval = f(xk);
        if (!isFinite(fval)) return NaN;
        sum += coeff * fval;
    }

    return sum / Math.pow(h, n);
}

// Get symbolic Taylor coefficients for known functions at ANY center point
// Returns array of coefficients c_k where Taylor series is Σ c_k * (x-a)^k
function getSymbolicCoefficients(funcStr, a, maxN) {
    const normalized = funcStr.replace(/\s/g, '');
    const coeffs = [];

    try {
        switch(normalized) {
            case 'sin(x)': {
                // Derivatives of sin at a cycle: sin(a), cos(a), -sin(a), -cos(a), ...
                const sinA = Math.sin(a);
                const cosA = Math.cos(a);
                const cycle = [sinA, cosA, -sinA, -cosA];
                for (let n = 0; n <= maxN; n++) {
                    coeffs.push(cycle[n % 4] / factorial(n));
                }
                return coeffs;
            }
            case 'cos(x)': {
                const sinA = Math.sin(a);
                const cosA = Math.cos(a);
                const cycle = [cosA, -sinA, -cosA, sinA];
                for (let n = 0; n <= maxN; n++) {
                    coeffs.push(cycle[n % 4] / factorial(n));
                }
                return coeffs;
            }
            case 'exp(x)': {
                const expA = Math.exp(a);
                for (let n = 0; n <= maxN; n++) {
                    coeffs.push(expA / factorial(n));
                }
                return coeffs;
            }
            case 'sinh(x)': {
                const sinhA = Math.sinh(a);
                const coshA = Math.cosh(a);
                for (let n = 0; n <= maxN; n++) {
                    const deriv = (n % 2 === 0) ? sinhA : coshA;
                    coeffs.push(deriv / factorial(n));
                }
                return coeffs;
            }
            case 'cosh(x)': {
                const sinhA = Math.sinh(a);
                const coshA = Math.cosh(a);
                for (let n = 0; n <= maxN; n++) {
                    const deriv = (n % 2 === 0) ? coshA : sinhA;
                    coeffs.push(deriv / factorial(n));
                }
                return coeffs;
            }
            case 'log(1+x)': {
                // Only valid for a > -1
                if (a <= -1) return null;
                // f^(n)(a) = (-1)^(n+1) * (n-1)! / (1+a)^n for n >= 1
                coeffs.push(Math.log(1 + a));
                for (let n = 1; n <= maxN; n++) {
                    const deriv = Math.pow(-1, n + 1) * factorial(n - 1) / Math.pow(1 + a, n);
                    coeffs.push(deriv / factorial(n));
                }
                return coeffs;
            }
            case '1/(1-x)': {
                // Only valid for a != 1
                if (Math.abs(a - 1) < 1e-10) return null;
                // f^(n)(a) = n! / (1-a)^(n+1)
                for (let n = 0; n <= maxN; n++) {
                    const deriv = factorial(n) / Math.pow(1 - a, n + 1);
                    coeffs.push(deriv / factorial(n));
                }
                return coeffs;
            }
            case 'atan(x)': {
                // Use numerical for non-zero center, symbolic only at 0
                if (Math.abs(a) > 1e-10) return null;
                for (let n = 0; n <= maxN; n++) {
                    if (n % 2 === 0) {
                        coeffs.push(0);
                    } else {
                        coeffs.push(Math.pow(-1, (n - 1) / 2) / n);
                    }
                }
                return coeffs;
            }
            case 'sqrt(1+x)': {
                // Use generalized binomial series
                // (1+x)^(1/2) = Σ C(1/2, n) * x^n where C(1/2, n) = (1/2)(1/2-1)...(1/2-n+1)/n!
                if (Math.abs(a) > 1e-10) return null; // Only at a=0 for now
                for (let n = 0; n <= maxN; n++) {
                    let coeff = 1;
                    for (let k = 0; k < n; k++) {
                        coeff *= (0.5 - k) / (k + 1);
                    }
                    coeffs.push(coeff);
                }
                return coeffs;
            }
            case 'tan(x)': {
                // tan has complex derivatives, use numerical
                return null;
            }
            default:
                return null;
        }
    } catch (e) {
        return null;
    }
}

// Compute Taylor coefficients numerically
function computeNumericalCoefficients(funcStr, a, maxN) {
    const coeffs = [];

    try {
        const compiled = math.compile(funcStr);
        const f = (x) => {
            try {
                const result = compiled.evaluate({ x: x });
                return isFinite(result) ? result : NaN;
            } catch {
                return NaN;
            }
        };

        for (let n = 0; n <= maxN; n++) {
            const deriv = numericalDerivative(f, a, n);
            if (!isFinite(deriv)) {
                coeffs.push(0);
            } else {
                coeffs.push(deriv / factorial(n));
            }
        }
    } catch (e) {
        return Array(maxN + 1).fill(0);
    }

    return coeffs;
}

// Main function to get Taylor coefficients
function getTaylorCoefficients(funcStr, a, maxN) {
  const symbolic = getSymbolicCoefficients(funcStr, a, maxN);
    if (symbolic) return symbolic;

    // Try symbolic differentiation for custom functions / non-covered centers
    const symDiff = computeSymbolicDiffCoefficients(funcStr, a, maxN);
    if (symDiff) return symDiff;

    // Fall back to numerical finite differences (least stable at high n)
    return computeNumericalCoefficients(funcStr, a, maxN);

}

// Evaluate Taylor polynomial at x
function evaluateTaylor(coeffs, a, x) {
    const dx = x - a;
    let result = 0;
    let power = 1;

    for (let k = 0; k < coeffs.length; k++) {
        result += coeffs[k] * power;
        power *= dx;
    }

    return result;
}

// GCD for fraction simplification
function gcd(a, b) {
    a = Math.abs(Math.round(a));
    b = Math.abs(Math.round(b));
    while (b) {
        const t = b;
        b = a % b;
        a = t;
    }
    return a || 1;
}

// Convert decimal to fraction if possible
function toFraction(decimal, maxDenom = 1000) {
    if (!isFinite(decimal)) return null;
    if (Math.abs(decimal) < 1e-12) return { num: 0, den: 1 };

    const sign = decimal < 0 ? -1 : 1;
    decimal = Math.abs(decimal);

    // Check if it's close to an integer
    const rounded = Math.round(decimal);
    if (Math.abs(decimal - rounded) < 1e-9) {
        return { num: sign * rounded, den: 1 };
    }

    // Try common denominators
    const denoms = [2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 32, 40, 48, 60, 64, 72, 80, 90, 100, 120, 128, 144, 180, 240, 360, 720];

    for (const d of denoms) {
        const n = decimal * d;
        if (Math.abs(n - Math.round(n)) < 1e-9) {
            const num = Math.round(n);
            const g = gcd(num, d);
            return { num: sign * (num / g), den: d / g };
        }
    }

    // Couldn't find nice fraction
    return null;
}

// Format coefficient as LaTeX
function formatCoeffLatex(coeff, power, a) {
    if (Math.abs(coeff) < 1e-12) return null;

    const sign = coeff >= 0 ? '+' : '-';
    const absCoeff = Math.abs(coeff);

    // Try to express as fraction
    const frac = toFraction(absCoeff);

    // Build x part
    const aVal = parseFloat(a.toFixed(4));
    let xPart = '';
    if (power > 0) {
        if (Math.abs(aVal) < 1e-6) {
            xPart = power === 1 ? 'x' : `x^{${power}}`;
        } else {
            const aStr = aVal > 0 ? `-${Math.abs(aVal)}` : `+${Math.abs(aVal)}`;
            xPart = power === 1 ? `(x${aStr})` : `(x${aStr})^{${power}}`;
        }
    }

    // Build coefficient part
    let coeffPart;
    if (frac) {
        if (frac.den === 1) {
            if (frac.num === 1 && power > 0) {
                coeffPart = '';
            } else {
                coeffPart = Math.abs(frac.num).toString();
            }
        } else {
            if (Math.abs(frac.num) === 1 && power > 0) {
                coeffPart = `\\frac{1}{${frac.den}}`;
            } else {
                coeffPart = `\\frac{${Math.abs(frac.num)}}{${frac.den}}`;
            }
        }
    } else {
        // Use decimal
        const formatted = absCoeff.toPrecision(4);
        if (formatted === '1' && power > 0) {
            coeffPart = '';
        } else {
            coeffPart = formatted;
        }
    }

    return { sign, coeff: coeffPart, xPart, term: coeffPart + xPart };
}

// Build general form LaTeX
function buildGeneralLatex(a, n) {
    const aVal = parseFloat(a.toFixed(2));
    const aStr = Math.abs(aVal) < 0.001 ? '' : (aVal > 0 ? `-${aVal}` : `+${Math.abs(aVal)}`);
    const xPart = Math.abs(aVal) < 0.001 ? 'x' : `(x${aStr})`;

    let terms = [`f(${aVal})`];
    if (n >= 1) terms.push(`f'(${aVal}) \\cdot ${xPart}`);
    if (n >= 2) terms.push(`\\frac{f''(${aVal})}{2!}${xPart}^{2}`);
    if (n >= 3) terms.push(`\\frac{f'''(${aVal})}{3!}${xPart}^{3}`);
    if (n >= 4) {
        terms.push(`\\cdots`);
        terms.push(`\\frac{f^{(${n})}(${aVal})}{${n}!}${xPart}^{${n}}`);
    }

    return `T_{${n}}(x) = ${terms.join(' + ')}`;
}

// Build expanded form LaTeX
function buildExpandedLatex(coeffs, a) {
    const terms = [];

    for (let k = 0; k < coeffs.length; k++) {
        const formatted = formatCoeffLatex(coeffs[k], k, a);
        if (formatted) {
            terms.push(formatted);
        }
    }

    if (terms.length === 0) return '0';

    let eq = terms[0].sign === '-' ? '-' + terms[0].term : terms[0].term;
    for (let i = 1; i < terms.length; i++) {
        eq += ` ${terms[i].sign} ${terms[i].term}`;
    }

    return eq;
}

function buildExpandedLatexMultiline(coeffs, a, n, termsPerLine = 4) {
    const formattedTerms = [];
    for (let k = 0; k < coeffs.length; k++) {
        const formatted = formatCoeffLatex(coeffs[k], k, a);
        if (formatted) formattedTerms.push(formatted);
    }

    if (formattedTerms.length === 0) {
        return `\\begin{aligned} T_{${n}}(x) &= 0 \\end{aligned}`;
    }

    // Turn each term into a signed token ("-x^2", "+ 3x", ...)
    const tokens = formattedTerms.map((t, i) => {
        if (i === 0) return (t.sign === '-') ? `-${t.term}` : `${t.term}`;
        return `${t.sign} ${t.term}`;
    });

    // Group tokens into lines
    const lines = [];
    for (let i = 0; i < tokens.length; i += termsPerLine) {
        lines.push(tokens.slice(i, i + termsPerLine).join(' '));
    }

    // Use aligned so KaTeX renders multiple lines cleanly
    // Repeating "&=" is fine and keeps alignment consistent.
    let out = `\\begin{aligned} T_{${n}}(x) &= ${lines[0]}`;
    for (let i = 1; i < lines.length; i++) {
        out += ` \\\\ &= ${lines[i]}`;
    }
    out += `\\end{aligned}`;

    return out;
}


// Generate plot data
function generateData() {
    const xMin = centerPoint - viewRange;
    const xMax = centerPoint + viewRange;
    const numPoints = 600;
    const step = (xMax - xMin) / numPoints;

    const xValues = [];
    const originalY = [];
    const taylorY = [];
    const errorY = [];

    // Get Taylor coefficients
    const coeffs = getTaylorCoefficients(currentFunction, centerPoint, numTerms);

    // Check for bad coefficients
    const maxCoeff = Math.max(...coeffs.map(c => Math.abs(c)));
    if (!isFinite(maxCoeff) || maxCoeff > 1e15) {
        // Coefficients are bad, likely numerical issues
        showError('Numerical instability detected. Try a different center point or function.');
        return null;
    }

    let compiled;
    try {
        compiled = math.compile(currentFunction);
    } catch (e) {
        showError('Invalid function syntax');
        return null;
    }

    let yMin = Infinity, yMax = -Infinity;

    for (let i = 0; i <= numPoints; i++) {
        const x = xMin + i * step;
        xValues.push(x);

        try {
            const origVal = compiled.evaluate({ x: x });
            const taylorVal = evaluateTaylor(coeffs, centerPoint, x);

            // Track y range from original function
            if (isFinite(origVal) && Math.abs(origVal) < 50) {
                yMin = Math.min(yMin, origVal);
                yMax = Math.max(yMax, origVal);
            }

            // Clamp for display
            const clampLimit = 20;
            const clampedOrig = (isFinite(origVal) && Math.abs(origVal) <= clampLimit) ? origVal : null;
            const clampedTaylor = (isFinite(taylorVal) && Math.abs(taylorVal) <= clampLimit * 2) ? taylorVal : null;

            originalY.push(clampedOrig);
            taylorY.push(clampedTaylor);

            if (isFinite(origVal) && isFinite(taylorVal)) {
                errorY.push(Math.abs(origVal - taylorVal));
            } else {
                errorY.push(null);
            }
        } catch (e) {
            originalY.push(null);
            taylorY.push(null);
            errorY.push(null);
        }
    }

    const generalLatex = buildGeneralLatex(centerPoint, numTerms);
    const expandedLatex = buildExpandedLatex(coeffs, centerPoint);

    // Calculate y range
    if (!isFinite(yMin)) yMin = -5;
    if (!isFinite(yMax)) yMax = 5;
    const padding = Math.max((yMax - yMin) * 0.15, 1);
    const yRange = [
        Math.max(-12, yMin - padding),
        Math.min(12, yMax + padding)
    ];

    return { xValues, originalY, taylorY, errorY, generalLatex, expandedLatex, yRange, coeffs };

}

// Show/hide error
function showError(msg) {
    if (elements.errorMessage) {
        elements.errorMessage.textContent = msg;
        elements.errorMessage.style.display = 'block';
    }
}

function hideError() {
    if (elements.errorMessage) {
        elements.errorMessage.style.display = 'none';
    }
}

// Toast notification
function showToast(msg) {
    if (elements.toast) {
        elements.toast.textContent = msg;
        elements.toast.classList.add('show');
        setTimeout(() => elements.toast.classList.remove('show'), 2000);
    }
}

function renderLatex(element, latex, { displayMode = false } = {}) {
    if (!element) return;

    if (katexReady && typeof katex !== 'undefined') {
        try {
            katex.render(latex, element, {
                throwOnError: false,
                displayMode
            });
        } catch (e) {
            element.textContent = latex;
        }
    } else {
        element.textContent = latex;
    }
}

function computeSymbolicDiffCoefficients(funcStr, a, maxN) {
    try {
        let node = math.parse(funcStr);

        const coeffs = [];
        for (let n = 0; n <= maxN; n++) {
            const compiled = node.compile();
            const derivAtA = compiled.evaluate({ x: a });

            if (!isFinite(derivAtA)) return null;

            coeffs.push(derivAtA / factorial(n));

            // Next derivative
            node = math.derivative(node, 'x');
        }
        return coeffs;
    } catch (e) {
        return null;
    }
}



// Main update function with graph animation support
function updatePlots(animate = false) {
    hideError();

    const data = generateData();
    if (!data) return;

    const { xValues, originalY, taylorY, errorY, generalLatex, expandedLatex, yRange, coeffs } = data;


    // Update LaTeX displays (no animation)
    // General: display mode (cleaner formatting)
    renderLatex(elements.latexGeneral, generalLatex, { displayMode: true });

    // Expanded: show multiline display, but keep a single-line version for copying
    const expandedRaw = `T_{${numTerms}}(x) = ${expandedLatex}`;
    const expandedDisplay = buildExpandedLatexMultiline(coeffs, centerPoint, numTerms, 4);

    currentLatex = expandedRaw; // keep copy behavior unchanged
    renderLatex(elements.latexExpanded, expandedDisplay, { displayMode: true });

    if (elements.latexRaw) elements.latexRaw.textContent = expandedRaw;


    // Main plot traces
    const traces = [
        {
            x: xValues,
            y: originalY,
            type: 'scatter',
            mode: 'lines',
            name: 'f(x) = ' + currentFunction,
            line: { color: '#ff6b6b', width: 3, shape: 'spline' },
            connectgaps: false
        },
        {
            x: xValues,
            y: taylorY,
            type: 'scatter',
            mode: 'lines',
            name: `T${numTerms}(x)`,
            line: { color: '#00d9ff', width: 2.5, shape: 'spline' },
            connectgaps: false
        },
        {
            x: [centerPoint],
            y: [(() => {
                try {
                    const y = math.evaluate(currentFunction, { x: centerPoint });
                    return isFinite(y) && Math.abs(y) < 20 ? y : 0;
                } catch { return 0; }
            })()],
            type: 'scatter',
            mode: 'markers',
            name: 'Center (a)',
            marker: { color: '#00ff88', size: 12, symbol: 'diamond' }
        }
    ];

    const layout = {
        paper_bgcolor: 'rgba(0,0,0,0)',
        plot_bgcolor: 'rgba(0,0,0,0.3)',
        font: { color: '#e8e8e8' },
        xaxis: {
            title: 'x',
            gridcolor: 'rgba(255,255,255,0.1)',
            zerolinecolor: 'rgba(255,255,255,0.3)',
            range: [centerPoint - viewRange, centerPoint + viewRange]
        },
        yaxis: {
            title: 'y',
            gridcolor: 'rgba(255,255,255,0.1)',
            zerolinecolor: 'rgba(255,255,255,0.3)',
            range: yRange
        },
        legend: { x: 0.02, y: 0.98, bgcolor: 'rgba(0,0,0,0.5)' },
        margin: { t: 30, r: 30, b: 50, l: 60 }
    };

    const plotEl = document.getElementById('plot');
    if (plotEl) {
        if (animate && animationSettings.enabled) {
            Plotly.animate('plot', {
                data: traces,
                layout: layout
            }, {
                transition: { duration: animationSettings.transitionDuration, easing: animationSettings.easing },
                frame: { duration: animationSettings.transitionDuration, redraw: true }
            }).catch(() => {
                // If animation fails, just do a regular update
                Plotly.react('plot', traces, layout, { responsive: true });
            });
        } else {
            Plotly.react('plot', traces, layout, { responsive: true });
        }
    }

    // Error plot (no animation needed)
    const errorTraces = [{
        x: xValues,
        y: errorY,
        type: 'scatter',
        mode: 'lines',
        fill: 'tozeroy',
        fillcolor: 'rgba(255, 217, 61, 0.3)',
        line: { color: '#ffd93d', width: 2 },
        connectgaps: false
    }];

    const errorLayout = {
        paper_bgcolor: 'rgba(0,0,0,0)',
        plot_bgcolor: 'rgba(0,0,0,0.3)',
        font: { color: '#e8e8e8' },
        xaxis: {
            gridcolor: 'rgba(255,255,255,0.1)',
            range: [centerPoint - viewRange, centerPoint + viewRange]
        },
        yaxis: {
            gridcolor: 'rgba(255,255,255,0.1)',
            type: 'log',
            range: [-10, 2]
        },
        showlegend: false,
        margin: { t: 10, r: 30, b: 30, l: 60 }
    };

    const errorEl = document.getElementById('error-plot');
    if (errorEl) {
        Plotly.react('error-plot', errorTraces, errorLayout, { responsive: true });
    }
}

// Toggle functions
function toggleErrorPlot() {
    elements.errorToggle?.classList.toggle('expanded');
    elements.errorContainer?.classList.toggle('expanded');
}

function toggleSliderSettings() {
    elements.sliderSettingsToggle?.classList.toggle('expanded');
    elements.sliderSettingsContent?.classList.toggle('expanded');
}

function toggleAnimationSettings() {
    elements.animationSettingsToggle?.classList.toggle('expanded');
    elements.animationSettingsContent?.classList.toggle('expanded');
}

// Update slider config
function updateSliderConfig(slider, minEl, maxEl, stepEl) {
    if (!slider || !minEl || !maxEl || !stepEl) return;

    const min = parseFloat(minEl.value);
    const max = parseFloat(maxEl.value);
    const step = parseFloat(stepEl.value);

    if (min < max && step > 0) {
        slider.min = min;
        slider.max = max;
        slider.step = step;

        const val = parseFloat(slider.value);
        if (val < min) slider.value = min;
        if (val > max) slider.value = max;
    }
}

// Copy LaTeX
async function copyLatex() {
    try {
        await navigator.clipboard.writeText(currentLatex);
        showToast('LaTeX copied!');
        if (elements.copyLatexBtn) {
            elements.copyLatexBtn.textContent = 'Copied!';
            setTimeout(() => elements.copyLatexBtn.textContent = 'Copy LaTeX', 2000);
        }
    } catch (e) {
        const ta = document.createElement('textarea');
        ta.value = currentLatex;
        document.body.appendChild(ta);
        ta.select();
        document.execCommand('copy');
        document.body.removeChild(ta);
        showToast('LaTeX copied!');
    }
}

// Animate terms
function animateTerms() {
    if (animationInterval) {
        clearInterval(animationInterval);
        animationInterval = null;
        if (elements.animateBtn) elements.animateBtn.textContent = 'Animate Terms';
        return;
    }

    if (elements.animateBtn) elements.animateBtn.textContent = 'Stop';

    const minTerm = parseInt(elements.termsSlider?.min) || 1;
    const maxTerm = parseInt(elements.termsSlider?.max) || 30;
    const stepVal = parseInt(elements.termsSlider?.step) || 1;
    let current = minTerm;

    animationInterval = setInterval(() => {
        if (elements.termsSlider) elements.termsSlider.value = current;
        if (elements.termsValue) elements.termsValue.textContent = current;
        numTerms = current;
        updatePlots(true);

        current += stepVal;
        if (current > maxTerm) {
            clearInterval(animationInterval);
            animationInterval = null;
            if (elements.animateBtn) elements.animateBtn.textContent = 'Animate Terms';
        }
    }, animationSettings.speed);
}

// Reset
function reset() {
    if (animationInterval) {
        clearInterval(animationInterval);
        animationInterval = null;
        if (elements.animateBtn) elements.animateBtn.textContent = 'Animate Terms';
    }

    centerPoint = 0;
    numTerms = 5;
    viewRange = 10;

    if (elements.centerSlider) elements.centerSlider.value = 0;
    if (elements.centerValue) elements.centerValue.textContent = '0';
    if (elements.termsSlider) elements.termsSlider.value = 5;
    if (elements.termsValue) elements.termsValue.textContent = '5';
    if (elements.rangeSlider) elements.rangeSlider.value = 10;
    if (elements.rangeValue) elements.rangeValue.textContent = '10';

    updatePlots(false);
}

// Setup event listeners
function setupEventListeners() {
    // Function selection
    elements.exampleSelect?.addEventListener('change', (e) => {
        if (e.target.value) {
            if (elements.functionInput) elements.functionInput.value = e.target.value;
            currentFunction = e.target.value;
            updatePlots(false);
        }
    });

    elements.functionInput?.addEventListener('input', (e) => {
        currentFunction = e.target.value || 'sin(x)';
        if (elements.exampleSelect) elements.exampleSelect.value = '';
        updatePlots(false);
    });

    // Sliders
    elements.centerSlider?.addEventListener('input', (e) => {
        centerPoint = parseFloat(e.target.value);
        if (elements.centerValue) elements.centerValue.textContent = centerPoint.toFixed(1);
        updatePlots(false); // No animation for center changes
    });

    elements.termsSlider?.addEventListener('input', (e) => {
        numTerms = parseInt(e.target.value);
        if (elements.termsValue) elements.termsValue.textContent = numTerms;
        updatePlots(true); // Animate for term changes
    });

    elements.rangeSlider?.addEventListener('input', (e) => {
        viewRange = parseFloat(e.target.value);
        if (elements.rangeValue) elements.rangeValue.textContent = viewRange;
        updatePlots(false); // No animation for range changes
    });

    // Slider config
    const configs = [
        { slider: elements.centerSlider, min: elements.centerMin, max: elements.centerMax, step: elements.centerStep },
        { slider: elements.termsSlider, min: elements.termsMin, max: elements.termsMax, step: elements.termsStep },
        { slider: elements.rangeSlider, min: elements.rangeMin, max: elements.rangeMax, step: elements.rangeStep }
    ];

    configs.forEach(c => {
        [c.min, c.max, c.step].forEach(el => {
            el?.addEventListener('change', () => updateSliderConfig(c.slider, c.min, c.max, c.step));
        });
    });

    // Animation settings
    elements.enableAnimations?.addEventListener('change', (e) => {
        animationSettings.enabled = e.target.checked;
    });

    elements.animationSpeedSelect?.addEventListener('change', (e) => {
        animationSettings.speed = parseInt(e.target.value);
    });

    elements.transitionDuration?.addEventListener('input', (e) => {
        animationSettings.transitionDuration = parseInt(e.target.value);
        if (elements.transitionValueDisplay) elements.transitionValueDisplay.textContent = `${e.target.value}ms`;
    });

    elements.easingFunction?.addEventListener('change', (e) => {
        animationSettings.easing = e.target.value;
    });

    // Buttons and toggles
    elements.animateBtn?.addEventListener('click', animateTerms);
    elements.resetBtn?.addEventListener('click', reset);
    elements.errorToggle?.addEventListener('click', toggleErrorPlot);
    elements.sliderSettingsToggle?.addEventListener('click', toggleSliderSettings);
    elements.animationSettingsToggle?.addEventListener('click', toggleAnimationSettings);
    elements.copyLatexBtn?.addEventListener('click', copyLatex);
}

// Initialize
async function init() {
    initDOMElements();

    await waitForKatex();
    katexReady = true;

    if (elements.functionInput) elements.functionInput.value = 'sin(x)';
    if (elements.exampleSelect) elements.exampleSelect.value = 'sin(x)';

    setupEventListeners();
    updatePlots(false);
}

// Start
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
} else {
    init();
}
