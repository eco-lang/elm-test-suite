import { createHash } from "node:crypto";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";

/** The sha256 of a file, in hex, for the translation manifest. */
export async function sha256File(path: string): Promise<string> {
  return createHash("sha256").update(readFileSync(path)).digest("hex");
}

/** The sha256 of a folder's files (their paths and contents, in sorted order), in hex: for the
 *  manifest's toolsSha256, so that a later job can tell whether the translator has changed. */
export async function sha256Tree(dir: string): Promise<string> {
  const files: string[] = [];
  const walk = (d: string) => {
    for (const name of readdirSync(d).sort()) {
      const p = join(d, name);
      if (statSync(p).isDirectory()) walk(p);
      else files.push(p);
    }
  };
  walk(dir);
  const hash = createHash("sha256");
  for (const f of files) {
    hash.update(f + "\n");
    hash.update(readFileSync(f));
  }
  return hash.digest("hex");
}
