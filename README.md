# NBA Meccsradar

A következő 7 nap NBA-meccseire ad becslést: ki nyer, hány pontot dob a két csapat, mennyi lesz az összpontszám.
A becslés statisztikából (ellenfél-korrigált erősség, szezonátlag, forma, pihenőnap, sérültek, hírek)
és 11 forrás fogadóirodai vonalaiból áll össze. A hírek 22 amerikai NBA-portálról jönnek.

A GitHub Actions félóránként lefuttatja, az eredmény a GitHub Pages oldalon látszik.

## Beállítás (egyszer)

1. Hozz létre egy új repót, és töltsd fel ennek a mappának a tartalmát (a `.github` mappát is).
2. **Settings → Pages → Build and deployment → Source: GitHub Actions**.
3. **Actions** fül → „NBA Meccsradar” → **Run workflow**. Az első futás pár perc (két szezon eredményeit tölti le).
4. Az oldal címe a futás után a Settings → Pages alatt, illetve a futás összefoglalójában látszik
   (`https://<felhasználónév>.github.io/<repó>/`).

Nem kötelező: ha van ingyenes kulcsod a the-odds-api.com oldalról, add meg
**Settings → Secrets and variables → Actions → New repository secret** alatt `ODDS_API_KEY` néven.
A program 6 óránként használja, így belefér a havi 500 kreditbe.

## Tudnivalók

- Privát repónál a GitHub Pages fizetős csomagot kér, és a havi ingyenes Actions-percek (2000) sem elegek
  félórás futáshoz. Nyilvános repóval mindkettő ingyenes. Ha privát kell, a workflowban ritkítsd az időzítést
  (pl. `cron: "7 */3 * * *"` = 3 óránként).
- Az előzmények (`data/games.json`, `data/nba_predikciok.json`) minden futás után visszakerülnek a repóba,
  ebből számolódik a Pontosság rész. Ezek a commitok tartják aktívan a repót is (a GitHub 60 nap tétlenség után
  leállítja az ütemezett futást).
- A futás oldalán (Actions → az adott futás) táblázatos összefoglaló látszik a következő meccsekről,
  a működő forrásokról és a hibákról.
- Helyben ugyanúgy indítható: `python nba_meccsradar.py` (élő szerver), vagy `--demo` kitalált adatokkal.

Ez szabályalapú elemzés, nem fogadási tanács.
