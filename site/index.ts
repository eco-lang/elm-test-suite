// KaTeX's stylesheet and fonts, for the mathematics of A Standard Definition of Elm?, which is
// rendered at build time (runner/definition-data.js); no KaTeX JavaScript runs in the browser.
import "katex/dist/katex.min.css";

type ElmPagesInit = {
  load: (elmLoaded: Promise<unknown>) => Promise<void>;
  flags: unknown;
};

const config: ElmPagesInit = {
  load: async function (elmLoaded) {
    await elmLoaded;
  },
  flags: function () {
    return null;
  },
};

export default config;
