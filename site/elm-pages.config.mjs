import { defineConfig } from "vite";

// A static site: every page is pre-rendered, so no adapter (server) is configured.
export default {
  vite: defineConfig({
    // The dev server (npm start) answers only to localhost unless a host is listed here.
    server: { allowedHosts: ["station.thesett.com"] },
  }),
  headTagsTemplate(context) {
    return `
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Montserrat:wght@600;700&family=Roboto+Mono:wght@400;500&family=Inter:wght@400;500;600&family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;0,8..60,700;1,8..60,400&display=swap" rel="stylesheet">
<meta name="generator" content="elm-pages v${context.cliVersion}" />
`;
  },
  preloadTagForFile(file) {
    return !file.endsWith(".css");
  },
};
