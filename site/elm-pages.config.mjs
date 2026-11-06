import { defineConfig } from "vite";

// A static site: every page is pre-rendered, so no adapter (server) is configured.
export default {
  vite: defineConfig({}),
  headTagsTemplate(context) {
    return `
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Montserrat:wght@600;700&family=Roboto+Mono:wght@400;500&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<meta name="generator" content="elm-pages v${context.cliVersion}" />
`;
  },
  preloadTagForFile(file) {
    return !file.endsWith(".css");
  },
};
