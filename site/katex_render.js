// Reads a JSON array of {tex, display} from stdin and writes a JSON array of HTML strings.
const katex = require("katex");

const macros = {
  "\\R": "\\mathbb{R}",
};

let input = "";
process.stdin.on("data", (d) => (input += d));
process.stdin.on("end", () => {
  const items = JSON.parse(input);
  const out = items.map(({ tex, display }) =>
    katex.renderToString(tex, {
      displayMode: display,
      throwOnError: true,
      output: "html",
      macros,
      strict: "ignore",
    })
  );
  process.stdout.write(JSON.stringify(out));
});
