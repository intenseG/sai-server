require("./classes/prototypes.js");
// const moment = require("moment");
const express = require("express");
const fileUpload = require("express-fileupload");
const bodyParser = require("body-parser");
const crypto = require("crypto");
const fs = require("fs-extra");
const MongoClient = require("mongodb").MongoClient;
const Long = require("mongodb").Long;
const ObjectId = require("mongodb").ObjectID;
const zlib = require("zlib");
const Cacheman = require("cacheman");
const app = express();
const Busboy = require("busboy");
const weight_parser = require("./classes/weight_parser.js");
const rss_generator = require("./classes/rss_generator.js");
const os = require("os");
const path = require("path");
const discord = require("./classes/discord");
const morgan = require("morgan");
const rfs = require("rotating-file-stream");
const dbutils = require("./classes/dbutils");
const mongoMorgan = require("mongo-morgan");
const Raven = require("raven");
const config = require("./configbsk");
const email_validator = require("email-validator");
const nodemailer = require("nodemailer");

const archiver = require("archiver");
const ini = require("ini");
const SGFParser = require("smartgame");

const configbsk = ini.parse(
  fs.readFileSync(__dirname + "/config.ini", "utf-8")
);
const default_visits = configbsk.default_visits
  ? Number(configbsk.default_visits)
  : 1600;
const default_randomcnt = configbsk.default_randomcnt
  ? Number(configbsk.default_randomcnt)
  : 30;
const default_resignation_percent = configbsk.default_resignation_percent
  ? Number(configbsk.default_resignation_percent)
  : 5;
const default_no_resignation_probability = configbsk.default_no_resignation_probability
  ? Number(configbsk.default_no_resignation_probability)
  : 0.1;
const default_komi = configbsk.default_komi
  ? Number(configbsk.default_komi)
  : 7.5;
const default_noise_value = configbsk.default_noise_value
  ? Number(configbsk.default_noise_value)
  : 0.03;
const default_lambda = configbsk.default_lambda
  ? Number(configbsk.default_lambda)
  : 0.5;
const default_other_options_selfplay = configbsk.default_other_options_selfplay
  ? String(configbsk.default_other_options_selfplay)
  : "";
const default_other_options_match = configbsk.default_other_options_match
  ? String(configbsk.default_other_options_match)
  : "";
const disable_default_selfplay = Boolean(configbsk.disable_default_selfplay);
const base_port = configbsk.base_port ? Number(configbsk.base_port) : 52515;
const instance_number = configbsk.instance_number
  ? Number(configbsk.instance_number)
  : 0;
const schedule_matches_to_all = configbsk.schedule_matches_to_all
  ? Boolean(configbsk.schedule_matches_to_all)
  : false;
const no_early_fail = configbsk.no_early_fail
  ? Boolean(configbsk.no_early_fail)
  : false;
const branching_coefficient = configbsk.branching_coefficient
  ? Number(configbsk.branching_coefficient)
  : 0.1;
const branching_maxbranches = configbsk.branching_maxbranches
  ? Number(configbsk.branching_maxbranches)
  : 3;

const MONGODB_URL = "mongodb://localhost/bsk0";

if (config.RAVEN_DSN) {
  console.log("init raven");
  Raven.config(config.RAVEN_DSN, {
    captureUnhandledRejections: true
  }).install();
}

/**
 * Request Logging
 */
const logDir = path.join(__dirname, "logs");
fs.ensureDirSync(logDir);
const logStream = rfs("access.log", {
  interval: "1d", // rotate daily
  maxFiles: 7, // keep 1 week worth of logs
  path: logDir
});
morgan.token("memory", () => {
  const used = process.memoryUsage();
  const usage = [];

  for (const key in used) {
    const size = (used[key] / 1024 / 1024).toFixed(2);

    usage.push(`${key}: ${size} MB`);
  }

  return usage.join(", ");
});
mongoMorgan.token("epochtime", () => Date.now());

// Save access log to `logs` collection
app.use(
  mongoMorgan(
    MONGODB_URL,
    "{'method': ':method', 'url': ':url', 'status': :status, 'response-time': :response-time, 'time': :epochtime}",
    { collection: "logs" }
  )
);

app.use(morgan("-->Before :memory", { stream: logStream, immediate: true }));
app.use(
  morgan(":method :url :status :req[content-length] :response-time ms", {
    stream: logStream,
    immediate: false
  })
);
app.use(morgan("-->After  :memory", { stream: logStream, immediate: false }));

/**
 * Utilities
 */
const {
  set_task_verification_secret,
  add_match_verification,
  check_match_verification,
  network_exists,
  checksum,
  make_seed,
  get_timestamp_from_seed,
  seed_from_mongolong,
  process_games_list,
  CalculateEloFromPercent,
  objectIdFromDate,
  log_memory_stats,
  SPRT,
  // LLR,
  asyncMiddleware,
  how_many_games_to_queue,
  add_gzip_hash
} = require("./classes/utilities.js");

const ELF_NETWORKS = [
  "62b5417b64c46976795d10a6741801f15f857e5029681a42d02c9852097df4b9",
  "d13c40993740cb77d85c838b82c08cc9c3f0fbc7d8c3761366e5d59e8f371cbd"
];

const auth_key = String(fs.readFileSync(__dirname + "/auth_key")).trim();
const public_auth_key = String(
  fs.readFileSync(__dirname + "/public_auth_key")
).trim();
set_task_verification_secret(
  String(fs.readFileSync(__dirname + "/task_secret")).trim()
);

const cacheIP24hr = new Cacheman("IP24hr");
const cacheIP1hr = new Cacheman("IP1hr");

// Cache information about matches and best network rating
const cachematches = new Cacheman("matches");
let bestRatings = new Map();

const fastClientsMap = new Map();

app.set("view engine", "pug");

// This shouldn't be needed but now and then when I restart test server, I see an uncaught ECONNRESET and I'm not sure
// where it is coming from. In case a server restart did the same thing, this should prevent a crash that would stop nodemon.
//
// It was a bug in nodemon which has now been fixed. It is bad practice to leave this here, eventually remove it.
//
process.on("uncaughtException", err => {
  console.error("Caught exception: " + err);
});

// https://blog.tompawlak.org/measure-execution-time-nodejs-javascript

let counter = 0;
let elf_counter = 0;
let best_network_mtimeMs = 0;
let best_network_hash_promise = null;
let db;

// TODO Make a map to store pending match info, use mapReduce to find who to serve out, only
// delete when SPRT fail or needed games have all arrived? Then we can update stats easily on
// all matches except just the current one (end of queue).
//
let pending_matches = [];
const MATCH_EXPIRE_TIME = 30 * 60 * 1000; // matches expire after 30 minutes. After that the match will be lost and an extra request will be made.

// Similar data for requested selfplays
let pending_selfplays = [];
const SELFPLAY_EXPIRE_TIME = 30 * 60 * 1000; // selfplays expire after 30 minutes. After that the selfplay will be lost and an extra request will be made.

const current_users = new Map();

function analyze_sgf_comments(comment) {
  // const [alpkt, alpkt0, beta, pi, avg_eval, avg_bonus, is_blunder] = comment.split(",").map(parseFloat);
  // console.log(alpkt + ", " + alpkt0 + ", " + beta + ", " + pi + ", " + avg_eval + ", " + avg_bonus + ", " + is_blunder);
  // const alpkt = comment.split(",").map(parseFloat);
  // for (let i = 0; i < alpkt.length; i++) {
  //   console.log(i + ": " + alpkt[i]);
  // }
  //    return  { priority: branching_coefficient*(0.25-avg_eval*(1-avg_eval)), komi: Math.round(alpkt) };
  // return { priority: branching_coefficient * 0.25, komi: default_komi };
  // if (alpkt == 0.0 && beta == 1.0) return { priority: 0.0, komi: default_komi };
  // console.log("New Komi: " + Math.round(alpkt));
  // return { priority: branching_coefficient * 0.25, komi: Math.round(alpkt) };
  const min = 0;
  const max = 15;
  const rnd_komi = Math.floor(Math.random() * (max + 1 - min)) + min + 0.5;
  // console.log("New Komi: " + rnd_komi);
  return { priority: branching_coefficient * 0.25, komi: rnd_komi };
}

function analyze_sgf(sgf) {
  const nodes = SGFParser.parse(sgf).gameTrees[0].nodes;
  const result = [];
  for (const pos in nodes) {
    if (pos == 0) continue;
    const value = analyze_sgf_comments(nodes[pos].C);
    result.unshift({
      move: Number(pos),
      rawvalues: nodes[pos].C,
      priority: value.priority,
      komi: value.komi
    });
  }
  result.sort((a, b) => b.priority - a.priority);
  return result;
}

function generate_branches(sgf) {
  const nodes = SGFParser.parse(sgf).gameTrees[0].nodes;
  const result = [];
  for (const pos in nodes) {
    if (result.length >= branching_maxbranches) break;
    if (pos == 0) continue;
    const value = analyze_sgf_comments(nodes[pos].C);
    if (Math.random() <= value.priority) {
      result.unshift({
        move: Number(pos),
        priority: value.priority,
        komi: value.komi
      });
    }
  }
  return result;
}

function get_options_hash(options) {
  if (options.visits) {
    return checksum(
      ""
        + options.visits
        + options.resignation_percent
        + options.noise
        + options.randomcnt
        + options.komi
        + options.noise_value
        + options.lambda
        + options.dumbpass
        + options.other_options
    ).slice(0, 6);
  } else {
    return checksum(
      ""
        + options.playouts
        + options.resignation_percent
        + options.noise
        + options.randomcnt
        + options.komi
        + options.noise_value
        + options.lambda
        + options.dumbpass
        + options.other_options
    ).slice(0, 6);
  }
}

async function get_fast_clients() {
  const start = Date.now();
  try {
    // Get some recent self-play games to calculate durations from seeds
    const games = await db
      .collection("games")
      .find({}, { ip: 1, movescount: 1, random_seed: 1 })
      .sort({ _id: -1 })
      .limit(1000)
      .toArray();

    // Keep track of the move rate of each game by client
    fastClientsMap.clear();
    games.forEach(game => {
      const seed = (s => (s instanceof Long ? s : new Long(s)))(
        game.random_seed
      );
      const startTime = get_timestamp_from_seed(seed);
      const minutes = (game._id.getTimestamp() / 1000 - startTime) / 60;

      // Make sure we have some reasonable duration
      if (minutes > 0 && minutes <= 60 * 24)
        fastClientsMap.set(game.ip, [
          ...(fastClientsMap.get(game.ip) || []),
          game.movescount / minutes
        ]);
    });

    // Clean up the map to be a single rate value with enough entries
    for (const [ip, rates] of fastClientsMap) {
      // Remove clients that submitted only a couple fast games (in case
      // some unexpected seed just happens to match the duration)
      if (rates.length < 3) fastClientsMap.delete(ip);
      else fastClientsMap.set(ip, rates.reduce((t, v) => t + v) / rates.length);
    }

    // Short circuit if there's nothing interesting to do
    if (fastClientsMap.size == 0) {
      console.log("No clients found with sufficient rate data");
      return;
    }

    // Print out some statistics on rates
    const sortedRates = [...fastClientsMap.values()].sort((a, b) => a - b);
    const quartile = n => {
      const index = (n / 4) * (sortedRates.length - 1);
      return index % 1 == 0
        ? sortedRates[index]
        : (sortedRates[Math.floor(index)] + sortedRates[Math.ceil(index)]) / 2;
    };
    console.log(
      "Client moves per minute rates:",
      ["min", "25%", "median", "75%", "max"]
        .map((text, index) => `${quartile(index).toFixed(1)} ${text}`)
        .join(", ")
    );

    // Keep only clients that have the top 25% rates
    const top25Rate = quartile(2);
    for (const [ip, rate] of fastClientsMap) {
      if (rate < top25Rate) fastClientsMap.delete(ip);
    }

    console.log(
      `In ${Date.now() - start}ms from recent ${games.length} games, found ${
        fastClientsMap.size
      } fast clients:`,
      fastClientsMap
    );
  } catch (err) {
    console.log("Failed to get recent games for fast clients:", err);
  }
}

//  db.matches.aggregate( [ { "$redact": { "$cond": [ { "$gt": [ "$number_to_play", "$game_count" ] }, "$$KEEP", "$$PRUNE" ] } } ] )
//
async function get_pending_matches() {
  pending_matches = [];

  return new Promise((resolve, reject) => {
    db.collection("matches")
      .aggregate([
        {
          $redact: {
            $cond: [
              { $gt: ["$number_to_play", "$game_count"] },
              "$$KEEP",
              "$$PRUNE"
            ]
          }
        }
      ])
      .sort({ _id: -1 })
      .forEach(
        match => {
          match.requests = []; // init request list.

          // Client only accepts strings for now
          //
          Object.keys(match.options).map(key => {
            match.options[key] = String(match.options[key]);
          });

          // If SPRT=pass use unshift() instead of push() so "Elo only" matches go last in priority
          //
          switch (SPRT(match.network1_wins, match.network1_losses)) {
            case false:
              if (no_early_fail) {
                pending_matches.unshift(match);
                console.log("SPRT fail: Unshifting: " + JSON.stringify(match));
              }
              break;
            case true:
              pending_matches.unshift(match);
              console.log("SPRT success: Unshifting: " + JSON.stringify(match));
              break;
            default:
              pending_matches.push(match);
              console.log("SPRT: Pushing: " + JSON.stringify(match));
          }
        },
        err => {
          if (err) {
            console.error("Error fetching matches: " + err);
            return reject(err);
          }
        }
      );
    resolve();
  });
}

//  db.self_plays.aggregate( [ { "$redact": { "$cond": [ { "$gt": [ "$number_to_play", "$game_count" ] }, "$$KEEP", "$$PRUNE" ] } } ] )
//
async function get_pending_selfplays() {
  const best_network_hash = await get_best_network_hash();
  pending_selfplays = [];

  return new Promise((resolve, reject) => {
    db.collection("self_plays")
      .aggregate([
        {
          $redact: {
            $cond: [
              {
                $and: [
                  { $gt: ["$number_to_play", "$game_count"] },
                  { $eq: ["$networkhash", best_network_hash] }
                ]
              },
              "$$KEEP",
              "$$PRUNE"
            ]
          }
        }
      ])
      .sort({ _id: -1 })
      .forEach(
        selfplay => {
          selfplay.requests = []; // init request list.
          pending_selfplays.unshift(selfplay);
        },
        err => {
          if (err) {
            console.error("Error fetching selfplays: " + err);
            return reject(err);
          }
        }
      );
    resolve();
  });
}

async function get_best_network_hash() {
  // Check if file has changed. If not, send cached version instead.
  //
  return fs
    .stat(__dirname + "/network/best-network.gz")
    .then(stats => {
      if (!best_network_hash_promise || best_network_mtimeMs != stats.mtimeMs) {
        best_network_mtimeMs = stats.mtimeMs;

        best_network_hash_promise = new Promise((resolve, reject) => {
          log_memory_stats("best_network_hash_promise begins");

          const rstream = fs.createReadStream(
            __dirname + "/network/best-network.gz"
          );
          const gunzip = zlib.createGunzip();
          const hash = crypto.createHash("sha256");

          hash.setEncoding("hex");

          log_memory_stats("Streams prepared");

          rstream
            .pipe(gunzip)
            .pipe(hash)
            .on("error", err => {
              console.error(
                "Error opening/gunzip/hash best-network.gz: " + err
              );
              reject(err);
            })
            .on("finish", () => {
              const best_network_hash = hash.read();
              log_memory_stats("Streams completed: " + best_network_hash);
              resolve(best_network_hash);
            });
        });
      }

      return best_network_hash_promise;
    })
    .catch(err => console.error(err));
}

async function get_current_users() {
  current_users.clear();
  const users = await db
    .collection("users")
    .find({ active: true }, { username: 1, password: 1 })
    .toArray();
  users.forEach(user => current_users.set(user.username, user.password));
}

// // eslint-disable-next-line no-unused-vars
// function validate_user(username, password, key) {
//    if (key && public_auth_key != "" && key == public_auth_key) return "";
// //   if (username && password && current_users.get(username) == password)
//     return username;
// //   return false;
// }

// eslint-disable-next-line no-unused-vars
function validate_user(username, key) {
  // if (key && public_auth_key != "" && key == public_auth_key) return "";
    if (username) {
      return username;
    } else {
      return "";
    }
    // return false;
}

const PESSIMISTIC_RATE = 0.4;

app.enable("trust proxy");

app.use(bodyParser.urlencoded({ extended: true }));
app.use(/\/((?!submit-network).)*/, fileUpload());

app.use("/view/player", express.static("static/eidogo-player-1.2/player"));
app.use("/viewmatch/player", express.static("static/eidogo-player-1.2/player"));
app.use("/view/wgo", express.static("static/wgo"));
app.use("/viewmatch/wgo", express.static("static/wgo"));
app.use("/static", express.static("static", { maxage: "365d", etag: true }));
app.use("/networks", express.static("network"));

// This is async but we don't need it to start the server. I'm calling it during startup so it'll get the value cached right away
// instead of when the first /best-network request comes in, in case a lot of those requests come in at once when server
// starts up.
get_best_network_hash().then(hash => console.log("Current best hash " + hash));

setInterval(() => {
  log_memory_stats("10 minute interval");

  get_fast_clients()
    .then()
    .catch();
}, 1000 * 60 * 10);

let last_match_db_check = Date.now();

setInterval(() => {
  const now = Date.now();

  // In case we have no matches scheduled, we check the db.
  //
  if (
    pending_matches.length === 0
    && now > last_match_db_check + 30 * 60 * 1000
  ) {
    console.log("No matches scheduled. Updating pending list.");

    last_match_db_check = now;

    get_pending_matches()
      .then()
      .catch();
  }
}, 1000 * 60 * 1);

let last_selfplay_db_check = Date.now();

setInterval(() => {
  const now = Date.now();

  // In case we have no selfplays scheduled, we check the db.
  //
  if (
    pending_selfplays.length === 0
    && now > last_selfplay_db_check + 30 * 60 * 1000
  ) {
    console.log("No self-plays scheduled. Updating pending list.");

    last_selfplay_db_check = now;

    get_pending_selfplays()
      .then()
      .catch();
  }
}, 1000 * 60 * 1);

MongoClient.connect(MONGODB_URL, (err, database) => {
  if (err) return console.log(err);

  db = database;

  db.collection("networks")
    .count()
    .then(count => {
      console.log(count + " networks.");
    });

  db.collection("networks").aggregate(
    [
      {
        $group: {
          _id: {
            type: {
              $cond: {
                if: { $in: ["$hash", ELF_NETWORKS] },
                then: "ELF",
                else: "LZ"
              }
            }
          },
          total: { $sum: "$game_count" }
        }
      }
    ],
    (err, res) => {
      if (err) console.log(err);

      get_fast_clients()
        .then()
        .catch();

      get_pending_matches()
        .then()
        .catch();

      get_pending_selfplays()
        .then()
        .catch();

      get_current_users()
        .then()
        .catch();

      res.forEach(result => {
        if (result._id.type == "ELF") elf_counter = result.total;
        else counter = result.total;
      });
      console.log(counter + " LZ games, " + elf_counter + " ELF games.");

      app.listen(base_port + instance_number, () => {
        console.log("listening on " + String(base_port + instance_number));
      });

      // Listening to both ports while /next people are moving over to real server address
      //
      // app.listen(8081, () => {
      //    console.log('listening on 8081')
      // });
    }
  );
});

// Obsolete
//
app.use(
  "/best-network-hash",
  asyncMiddleware(async(req, res) => {
    const hash = await get_best_network_hash();

    res.write(hash);
    res.write("\n");
    // Can remove if autogtp no longer reads this. Required client and leelza versions are in get-task now.
    res.write("11");
    res.end();
  })
);

// Server will promote a network.
//
app.post(
  "/promote",
  // eslint-disable-next-line no-unused-vars
  asyncMiddleware(async(req, res, next) => {
    if (!req.body.key || req.body.key != auth_key) {
      console.log(
        "AUTH FAIL: '"
          + String(req.body.key)
          + "' VS '"
          + String(auth_key)
          + "'"
      );

      return res.status(400).send("Incorrect key provided.");
    }

    if (!req.body.hash)
      return res.status(400).send("Network hash not provided.");
    fs.copyFileSync(
      __dirname + "/network/" + req.body.hash + ".gz",
      __dirname + "/network/best-network.gz"
    );
    await get_pending_selfplays();
    res.send("Network has been promoted");
  })
);

// Server will copy a new best-network to the proper location if validation testing of an uploaded network shows
// it is stronger than the prior network. So we don't need to worry about locking the file/etc when uploading to
// avoid an accidential download of a partial upload.
//
// This is no longer used, as /network/ is served by nginx and best-network.gz downloaded directly from it
//
app.use(
  "/best-network",
  asyncMiddleware(async(req, res) => {
    const hash = await get_best_network_hash();
    const readStream = fs.createReadStream(
      __dirname + "/network/best-network.gz"
    );

    readStream.on("error", err => {
      res.send("Error: " + err);
      console.error("ERROR /best-network : " + err);
    });

    readStream.on("open", () => {
      res.setHeader(
        "Content-Disposition",
        "attachment; filename=" + hash + ".gz"
      );
      res.setHeader("Content-Transfer-Encoding", "binary");
      res.setHeader("Content-Type", "application/octet-stream");
    });

    readStream.pipe(res);

    console.log(
      req.ip
        + " ("
        + req.headers["x-real-ip"]
        + ") "
        + " downloaded /best-network"
    );
  })
);

app.post(
  "/best-network-chunks",
  // eslint-disable-next-line no-unused-vars
  asyncMiddleware(async(req, res, next) => {
    if (!req.body.key || req.body.key != auth_key) {
      console.log(
        "AUTH FAIL: '"
          + String(req.body.key)
          + "' VS '"
          + String(auth_key)
          + "'"
      );

      return res.status(400).send("Incorrect key provided.");
    }

    let game_count = 0;
    let chunk_count = 0;
    let chunk = "";
    const hash = req.body.hash || (await get_best_network_hash());

    function write_chunk() {
      const filename
        = "train_" + hash.substring(0, 8) + "_" + chunk_count + ".gz";
      console.log("New  " + filename + " Chunk " + chunk_count + " written");
      zip.append(zlib.gzipSync(chunk), { name: filename });
      game_count = 0;
      chunk_count += 1;
      chunk = "";
    }

    res.writeHead(200, {
      "Content-Type": "application/zip",
      "Content-disposition": "attachment; filename=chunks.zip"
    });
    const zip = archiver("zip");
    zip.pipe(res);
    db.collection("games")
      .find({ networkhash: hash }, { _id: false, data: true })
      .limit(275000)
      .forEach(
        match => {
          chunk += match.data;
          game_count += 1;
          if (game_count >= 64) write_chunk();
        },
        err => {
          if (err) return res("Error fetching games: " + err);
          else if (game_count > 0) write_chunk();
          zip.finalize();
        }
      );
  })
);

app.post("/request-match", (req, res) => {
  // "number_to_play" : 200, "options" : { "playouts" : 1601, "resignation_percent" : 1, "randomcnt" : 0, "noise" : "false" }

  if (!req.body.key || req.body.key != auth_key) {
    console.log(
      "AUTH FAIL: '" + String(req.body.key) + "' VS '" + String(auth_key) + "'"
    );

    return res.status(400).send("Incorrect key provided.");
  }

  if (!req.body.network1)
    return res.status(400).send("No network1 hash specified.");
  else if (!network_exists(req.body.network1))
    return res.status(400).send("network1 hash not found.");

  if (!req.body.network2) req.body.network2 = null;
  else if (!network_exists(req.body.network2))
    return res.status(400).send("network2 hash not found.");

  // TODO Need to support new --visits flag as an alternative to --playouts. Use visits if both are missing? Don't allow both to be set.
  //
  if (req.body.playouts && req.body.visits)
    return res.status(400).send("Please set only playouts or visits, not both");

  if (!req.body.playouts && !req.body.visits)
    //req.body.playouts = 1600;
    req.body.visits = default_visits;
  //return res.status(400).send('No playouts specified.');

  if (!req.body.resignation_percent)
    req.body.resignation_percent = default_resignation_percent;
  //return res.status(400).send('No resignation_percent specified.');

  if (!req.body.noise) req.body.noise = false;
  //return res.status(400).send('No noise specified.');

  if (!req.body.randomcnt) req.body.randomcnt = 30;
  //return res.status(400).send('No randomcnt specified.');

  if (!req.body.number_to_play) req.body.number_to_play = 200;
  //return res.status(400).send('No number_to_play specified.');

  if (!req.body.komi) req.body.komi = default_komi;

  if (!req.body.lambda) req.body.lambda = default_lambda;

  if (!req.body.dumbpass) req.body.dumbpass = String(config.default_dumbpass);

  if (!req.body.acceleration_endgame) req.body.acceleration_endgame = false;

  if (!("other_options" in req.body))
    req.body.other_options = default_other_options_match;

  const options = {
    resignation_percent: Number(req.body.resignation_percent),
    randomcnt: Number(req.body.randomcnt),
    noise: String(req.body.noise),
    komi: Number(req.body.komi),
    lambda: Number(req.body.lambda),
    dumbpass: req.body.dumbpass.toLowerCase() === "true",
    acceleration_endgame: req.body.acceleration_endgame.toLowerCase() === "true",
    other_options: String(req.body.other_options)
  };

  if (req.body.playouts) {
    options.playouts = Number(req.body.playouts);
  }

  if (req.body.visits) {
    options.visits = Number(req.body.visits);
  }

  // Usage:
  //   - schedule a Test match, set is_test=true or is_test=1
  //   curl -F is_test=true <other params>
  //
  //   - schedule a Normal match, leave out the flag
  //   curl  <other params>
  //
  req.body.is_test = ["true", "1"].includes(req.body.is_test);

  const match = {
    network1: req.body.network1,
    network2: req.body.network2,
    network1_losses: 0,
    network1_wins: 0,
    game_count: 0,
    number_to_play: Number(req.body.number_to_play),
    is_test: req.body.is_test,
    options,
    options_hash: get_options_hash(options)
  };

  db.collection("matches")
    .insertOne(match)
    .then(() => {
      // Update cache
      dbutils.clear_matches_cache();

      // Client only accepts strings for now
      Object.keys(match.options).map(key => {
        match.options[key] = String(match.options[key]);
      });

      match.requests = []; // init request list.
      pending_matches.unshift(match);

      console.log(
        req.ip + " (" + req.headers["x-real-ip"] + ") " + " Match added!"
      );
      res.send((match.is_test ? "Test" : "Regular") + " Match added!\n");
      console.log("Pending is now: " + JSON.stringify(pending_matches));
    })
    .catch(err => {
      console.error(
        req.ip
          + " ("
          + req.headers["x-real-ip"]
          + ") "
          + " ERROR: Match addition failed: "
          + err
      );
      res.send("ERROR: Match addition failed\n");
    });
});

// curl -F 'weights=@zero.prototxt' -F 'training_count=175000' http://localhost:52516/submit-network
//
// Detect if network already exists and if so, inform the uploader and don't overwrite?
// So we don't think the network is newer than it really is. Actually, upsert shouldn't change
// the ObjectID so date will remain original insertion date.
//
app.post(
  "/submit-network",
  asyncMiddleware((req, res) => {
    log_memory_stats("submit network start");
    const busboy = new Busboy({ headers: req.headers });

    req.body = {};

    let file_promise = null;

    req
      .pipe(busboy)
      .on("field", (name, value) => {
        req.body[name] = value;
      })
      .on("file", (name, file_stream, file_name) => {
        if (!req.files) req.files = {};

        if (name != "weights") {
          // Not the file we expected, flush the stream and do nothing
          //
          file_stream.on("readable", file_stream.read);
          return;
        }

        const temp_file = path.join(os.tmpdir(), file_name);
        // Pipes
        //   - file_stream.pipe(fs_stream)
        //   - file_stream.pipe(gunzip_stream)
        //       - gunzip_stream.pipe(hasher)
        //       - gunzip_stream.pipe(parser)
        file_promise = new Promise((resolve, reject) => {
          const fs_stream = file_stream
            .pipe(fs.createWriteStream(temp_file))
            .on("error", reject);
          const gunzip_stream = file_stream
            .pipe(zlib.createGunzip())
            .on("error", reject);

          Promise.all([
            new Promise(resolve => {
              fs_stream.on("finish", () => resolve({ path: fs_stream.path }));
            }),
            new Promise(resolve => {
              const hasher = gunzip_stream
                .pipe(crypto.createHash("sha256"))
                .on("finish", () => resolve({ hash: hasher.read().toString("hex") })
                );
            }),
            new Promise(resolve => {
              const parser = gunzip_stream
                .pipe(new weight_parser())
                .on("finish", () => resolve(parser.read()));
            })
          ]).then(results => {
            // consolidate results
            results = req.files[name] = Object.assign.apply(null, results);

            // Move temp file to network folder with hash name
            results.path = path.join(
              __dirname,
              "network",
              results.hash + ".gz"
            );
            if (fs.existsSync(temp_file))
              fs.moveSync(temp_file, results.path, { overwrite: true });

            // We are all done (hash, parse and save file)
            resolve();
          });
        }).catch(err => {
          console.error(err);
          req.files[name] = { error: err };

          // Clean up, flush stream and delete temp file
          file_stream.on("readable", file_stream.read);

          if (fs.existsSync(temp_file)) fs.removeSync(temp_file);
        });
      })
      .on("finish", async() => {
        await file_promise;

        if (!req.body.key || req.body.key != auth_key) {
          console.log(
            "AUTH FAIL: '"
              + String(req.body.key)
              + "' VS '"
              + String(auth_key)
              + "'"
          );
          return res.status(400).send("Incorrect key provided.");
        }

        if (!req.files || !req.files.weights)
          return res.status(400).send("No weights file was uploaded.");

        if (req.files.weights.error)
          return res.status(400).send(req.files.weights.error.message);

        const set = {
          hash: req.files.weights.hash,
          ip: req.ip,
          training_count: +req.body.training_count || null,
          training_steps: +req.body.training_steps || null,
          filters: +req.body.filters || req.files.weights.filters,
          blocks: +req.body.blocks || req.files.weights.blocks,
          training_run: +req.body.training_run || null,
          generation: +req.body.generation || null,
          parent_hash: req.body.parent_hash,
          description: req.body.description
        };

        // No training count given, we'll calculate it from database.
        //
        if (!set.training_count) {
          const cursor = db
            .collection("networks")
            .aggregate([{ $group: { _id: 1, count: { $sum: "$game_count" } } }]);
          const totalgames = await cursor.next();
          if (totalgames) set.training_count = totalgames.count;
          else set.training_count = 0;
        }

        // Prepare variables for printing messages
        //
        const { blocks, filters, hash, training_count } = set;

        db.collection("networks").updateOne(
          { hash: set.hash },
          { $set: set },
          { upsert: true },
          (err, dbres) => {
            if (err) {
              res.end(err.message);
              console.error(err);
            } else {
              const msg
                = "Network weights ("
                + blocks
                + " x "
                + filters
                + ") "
                + hash
                + " ("
                + training_count
                + ") "
                + (dbres.upsertedCount == 0 ? "exists" : "uploaded")
                + "!";
              res.end(msg);
              console.log(msg);
              log_memory_stats("submit network ends");
            }
          }
        );
      });
  })
);

app.post(
  "/submit-match",
  asyncMiddleware(async(req, res) => {
    const logAndFail = msg => {
      console.log(
        `${req.ip} (${req.headers["x-real-ip"]})/submit-match: ${msg}`
      );
      console.log(
        `files: ${JSON.stringify(
          Object.keys(req.files || {})
        )}, body: ${JSON.stringify(req.body)}`
      );
      return res.status(400).send(msg);
    };

    const user_name = validate_user(
      req.body.username,
      req.body.key
    );

    if (user_name === false) return logAndFail("Invalid authentication.");

    if (!req.files) return logAndFail("No files were uploaded.");

    if (!req.files.sgf) return logAndFail("No sgf file provided.");

    if (!req.body.clientversion)
      return logAndFail("No clientversion provided.");

    if (!req.body.winnerhash) return logAndFail("No winner hash provided.");

    if (!req.body.loserhash) return logAndFail("No loser hash provided.");

    if (!req.body.winnercolor) return logAndFail("No winnercolor provided.");

    if (!req.body.movescount) return logAndFail("No movescount provided.");

    if (!req.body.score) return logAndFail("No score provided.");

    if (!req.body.options_hash) return logAndFail("No options_hash provided.");

    if (!req.body.random_seed) return logAndFail("No random_seed provided.");

    if (!check_match_verification(req.body))
      return logAndFail("Verification failed.");

    // Convert random_seed to Long, which is signed, after verifying the string
    req.body.random_seed = Long.fromString(req.body.random_seed, 10);
    req.body.task_time = get_timestamp_from_seed(req.body.random_seed);

    // verify match exists in database
    let match = await db.collection("matches").findOne({
      $or: [
        { network1: req.body.winnerhash, network2: req.body.loserhash },
        { network2: req.body.winnerhash, network1: req.body.loserhash }
      ],
      options_hash: req.body.options_hash
    });

    // Match not found, abort!!
    if (!match) return logAndFail("Match not found.");

    // Verify random_seed for the match hasn't been used
    if (
      await db.collection("match_games").findOne({
        random_seed: req.body.random_seed,
        $or: [
          { winnerhash: req.body.winnerhash, loserhash: req.body.loserhash },
          { loserhash: req.body.winnerhash, winnerhash: req.body.loserhash }
        ],
        options_hash: req.body.options_hash
      })
    )
      return logAndFail("Upload match with duplicate random_seed.");

    // calculate sgfhash
    try {
      const sgfbuffer = await new Promise((resolve, reject) => zlib.unzip(req.files.sgf.data, (err, res) => {
          if (err) {
            reject(err);
          } else {
            resolve(res);
          }
        })
      );
      const sgfhash = checksum(sgfbuffer, "sha256");

      // upload match game to database
      const dbres = await db.collection("match_games").updateOne(
        { sgfhash },
        {
          $set: {
            ip: req.ip,
            winnerhash: req.body.winnerhash,
            loserhash: req.body.loserhash,
            sgf: sgfbuffer.toString(),
            options_hash: req.body.options_hash,
            clientversion: Number(req.body.clientversion),
            winnercolor: req.body.winnercolor,
            movescount: req.body.movescount
              ? Number(req.body.movescount)
              : null,
            score: req.body.score,
            random_seed: req.body.random_seed,
            username: user_name
          }
        },
        { upsert: true }
      );

      // Not inserted, we got duplicate sgfhash, abort!
      if (!dbres.upsertedId)
        return logAndFail("Upload match with duplicate sgf.");

      console.log(
        `${req.ip} (${req.headers["x-real-ip"]}) uploaded in ${Math.round(
          Date.now() / 1000 - req.body.task_time
        )}s match: ${sgfhash}`
      );
      res.send("Match data " + sgfhash + " stored in database\n");
    } catch (err) {
      console.error(err);
      return logAndFail("Error with sgf.");
    }

    // prepare $inc
    const $inc = { game_count: 1 };
    const winner_net
      = req.body.winnercolor == "jigo"
        ? 0
        : match.network1 == req.body.winnerhash
        ? 1
        : 2;
    if (winner_net == 1) $inc.network1_wins = 1;
    else if (winner_net == 2) $inc.network1_losses = 1;

    // save to database using $inc and get modified document
    match = (await db.collection("matches").findOneAndUpdate(
      { _id: match._id },
      { $inc },
      { returnOriginal: false } // return modified document
    )).value;

    // get latest SPRT result
    const sprt_result = SPRT(match.network1_wins, match.network1_losses);
    const pending_match_index = pending_matches.findIndex(m => m._id.equals(match._id)
    );

    // match is found in pending_matches
    if (pending_match_index >= 0) {
      const m = pending_matches[pending_match_index];

      if (sprt_result === false && !no_early_fail) {
        // remove from pending matches
        console.log("SPRT: Early fail pop: " + JSON.stringify(m));
        pending_matches.splice(pending_match_index, 1);
        console.log(
          "SPRT: Early fail post-pop: " + JSON.stringify(pending_matches)
        );
      } else {
        // remove the match from the requests array.
        const index = m.requests.findIndex(
          e => e.seed === seed_from_mongolong(req.body.random_seed)
        );
        if (index !== -1) {
          m.requests.splice(index, 1);
        }

        // update stats
        m.game_count++;
        if (m.network1 == req.body.winnerhash) {
          m.network1_wins++;
        } else {
          m.network1_losses++;
        }

        // Check > 1 since we'll run to 200 even on a SPRT pass, but will do it at end.
        //
        if (
          (sprt_result === true || sprt_result === false)
          && pending_matches.length > 1
        ) {
          console.log("SPRT: Early pass unshift: " + JSON.stringify(m));
          pending_matches.splice(pending_match_index, 1); // cut out the match
          if (m.game_count < m.number_to_play) pending_matches.unshift(m); // continue a SPRT pass at end of queue
          console.log(
            "SPRT: Early pass post-unshift: " + JSON.stringify(pending_matches)
          );
        }
      }
    }

    // Lastly, promotion check!!
    const best_network_hash = await get_best_network_hash();
    if (
      // Best network was being challenged
      match.network2 == best_network_hash
      // This is not a test match
      && !match.is_test
      // SPRT passed OR it has reach 55% after 200 games (stick to the magic number)
      && (sprt_result === true
        // || (match.game_count >= 200 && match.network1_wins / match.game_count >= 0.55))
        || (match.game_count >= 200
          && match.network1_wins
            >= match.game_count / 2 + Math.sqrt(match.game_count)))
    ) {
      const promote_hash = match.network1;
      const promote_file = `${__dirname}/network/${promote_hash}.gz`;
      fs.copyFileSync(promote_file, __dirname + "/network/best-network.gz");
      console.log(`New best network copied from ${promote_file}`);
      discord.network_promotion_notify(promote_hash);
    }

    try {
      dbutils.update_matches_stats_cache(db, match._id, winner_net);
      cachematches.clear(() => console.log("Cleared match cache."));
    } catch (err) {
      console.error(err);
      return logAndFail("Error with update_matches_stats_cache.");
    }
  })
);

// curl -F 'networkhash=abc123' -F 'file=@zero.prototxt' http://localhost:52516/submit
// curl -F 'networkhash=abc123' -F 'sgf=@zero.prototxt' -F 'trainingdata=@zero.prototxt' http://localhost:52516/submit

app.post("/submit", (req, res) => {
  const logAndFail = msg => {
    console.log(`${req.ip} (${req.headers["x-real-ip"]}) /submit: ${msg}`);
    console.log(
      `files: ${JSON.stringify(
        Object.keys(req.files || {})
      )}, body: ${JSON.stringify(req.body)}`
    );
    return res.status(400).send(msg);
  };

  const user_name = validate_user(
    req.body.username,
    req.body.key
  );

  if (user_name === false) return logAndFail("Invalid authentication.");

  if (!req.files) return logAndFail("No files were uploaded.");

  if (!req.files.sgf) return logAndFail("No sgf file provided.");

  if (!req.files.trainingdata)
    return logAndFail("No trainingdata file provided.");

  if (!req.body.clientversion) return logAndFail("No clientversion provided.");

  if (!req.body.networkhash) return logAndFail("No network hash provided.");

  if (!req.body.winnercolor) return logAndFail("No winnercolor provided.");

  if (!req.body.movescount) return logAndFail("No movescount provided.");

  if (!req.body.options_hash) return logAndFail("No options_hash provided.");

  if (!req.body.random_seed) return logAndFail("No random_seed provided.");

  req.body.random_seed = Long.fromString(req.body.random_seed, 10);
  req.body.task_time = get_timestamp_from_seed(req.body.random_seed);

  const clientversion = req.body.clientversion;
  const networkhash = req.body.networkhash;
  let trainingdatafile;
  let sgffile;
  let sgfhash;

  const sgfbuffer = Buffer.from(req.files.sgf.data);
  const trainbuffer = Buffer.from(req.files.trainingdata.data);

  if (req.ip == "xxx") {
    res.send("Game data " + sgfhash + " stored in database\n");
    console.log(
      "FAKE/SPAM reply sent to " + "xxx" + " (" + req.headers["x-real-ip"] + ")"
    );
  } else {
    zlib.unzip(sgfbuffer, (err, sgfbuffer) => {
      if (err) {
        console.error(err);
        return logAndFail("Error with sgf.");
      } else {
        sgffile = sgfbuffer.toString();
        sgfhash = checksum(sgffile, "sha256");

        zlib.unzip(trainbuffer, (err, trainbuffer) => {
          if (err) {
            console.error(err);
            return logAndFail("Error with trainingdata.");
          } else {
            trainingdatafile = trainbuffer.toString();

            db.collection("games").updateOne(
              { sgfhash },
              {
                $set: {
                  ip: req.ip,
                  networkhash,
                  sgf: sgffile,
                  options_hash: req.body.options_hash,
                  movescount: req.body.movescount
                    ? Number(req.body.movescount)
                    : null,
                  options: req.body.options
                    ? JSON.parse(req.body.options)
                    : null,
                  data: trainingdatafile,
                  clientversion: Number(clientversion),
                  winnercolor: req.body.winnercolor,
                  random_seed: req.body.random_seed,
                  selfplay_id: req.body.selfplay_id,
                  username: user_name
                }
              },
              { upsert: true },
              err => {
                // Need to catch this better perhaps? Although an error here really is totally unexpected/critical.
                //
                if (err) {
                  console.log(
                    req.ip
                      + " ("
                      + req.headers["x-real-ip"]
                      + ") "
                      + " uploaded game #"
                      + counter
                      + ": "
                      + sgfhash
                      + " ERROR: "
                      + err
                  );
                  res.send("Game data " + sgfhash + " stored in database\n");
                } else {
                  let message = `in ${Math.round(
                    Date.now() / 1000 - req.body.task_time
                  )}s `;
                  if (ELF_NETWORKS.includes(networkhash)) {
                    elf_counter++;
                    message += `ELF game #${elf_counter}`;
                  } else {
                    counter++;
                    message += `LZ game #${counter}`;
                  }
                  console.log(
                    `${req.ip} (${
                      req.headers["x-real-ip"]
                    }) uploaded ${message}: ${sgfhash}`
                  );
                  res.send("Game data " + sgfhash + " stored in database\n");
                }
              }
            );

            db.collection("networks").updateOne(
              { hash: networkhash },
              { $inc: { game_count: 1 } },
              {},
              err => {
                if (err) {
                  if (ELF_NETWORKS.includes(networkhash))
                    console.log(
                      req.ip
                        + " ("
                        + req.headers["x-real-ip"]
                        + ") "
                        + " uploaded ELF game #"
                        + elf_counter
                        + ": "
                        + sgfhash
                        + " INCREMENT ERROR: "
                        + err
                    );
                  else
                    console.log(
                      req.ip
                        + " ("
                        + req.headers["x-real-ip"]
                        + ") "
                        + " uploaded LZ game #"
                        + counter
                        + ": "
                        + sgfhash
                        + " INCREMENT ERROR: "
                        + err
                    );
                } else {
                  //console.log("Incremented " + networkhash);
                }
              }
            );

            if (req.body.selfplay_id) {
              const selfplay_id = ObjectId(req.body.selfplay_id);
              db.collection("self_plays").updateOne(
                { _id: selfplay_id },
                { $inc: { game_count: 1 } },
                {},
                // eslint-disable-next-line no-unused-vars
                (err, dbres) => {
                  if (err)
                    console.log(
                      req.ip
                        + " ("
                        + req.headers["x-real-ip"]
                        + ") "
                        + " selfplay "
                        + selfplay_id
                        + " INCREMENT ERROR: "
                        + err
                    );
                }
              );

              const selfplay_index = pending_selfplays.findIndex(
                s => s._id == req.body.selfplay_id
              );
              if (selfplay_index != -1) {
                const selfplay = pending_selfplays[selfplay_index];
                const request_index = selfplay.requests.findIndex(
                  e => e.seed === seed_from_mongolong(req.body.random_seed)
                );
                if (request_index !== -1) {
                  selfplay.requests.splice(request_index, 1);
                }
                selfplay.game_count++;
                if (selfplay.game_count >= selfplay.number_to_play) {
                  pending_selfplays.splice(selfplay_index, 1);
                }
              }
            }

            get_best_network_hash().then(hash => {
              if (hash == networkhash) {
                // only create branches if the game corresponds to the current best network hash
                // to avoid long sequences of self-play with old networks.
                const branches = generate_branches(sgffile);
                if (branches.length > 0) {
                  const selfplay_promise = req.body.selfplay_id
                    ? db
                        .collection("self_plays")
                        .findOne({ _id: ObjectId(req.body.selfplay_id) })
                    : Promise.resolve(null);
                  selfplay_promise
                    .then(selfplay => {
                      for (const branch of branches) {
                        console.log("Ayasii EX -> " + String(branch.komi));
                        const set = {
                          priority: branch.priority,
                          komi: branch.komi,
                          // komi: selfplay
                          //   ? selfplay.komi + branch.komi
                          //   : default_komi + branch.komi,
                          noise_value: selfplay
                            ? selfplay.noise_value
                            : default_noise_value,
                          lambda: selfplay ? selfplay.lambda : default_lambda,
                          dumbpass:
                            selfplay && "dumbpass" in selfplay
                              ? selfplay.dumbpass
                              : config.default_dumbpass,
                          visits: selfplay ? selfplay.visits : default_visits,
                          resignation_percent: selfplay
                            ? selfplay.resignation_percent
                            : default_resignation_percent,
                          no_resignation_probability: selfplay
                            ? selfplay.no_resignation_probability
                            : default_no_resignation_probability,
                          other_options: selfplay
                            ? selfplay.other_options
                            : default_other_options_selfplay,
                          number_to_play: 1,
                          game_count: 0,
                          networkhash,
                          sgfhash,
                          movescount: branch.move,
                          ip: req.headers["x-real-ip"] || req.ip
                        };

                        db.collection("self_plays").insertOne(
                          set,
                          {},
                          // eslint-disable-next-line no-unused-vars
                          (err, dbres) => {
                            if (err)
                              console.log(
                                req.ip
                                  + " ("
                                  + req.headers["x-real-ip"]
                                  + ") "
                                  + " LZ game #"
                                  + counter
                                  + ": error adding branch"
                              );
                            else
                              console.log(
                                req.ip
                                  + " ("
                                  + req.headers["x-real-ip"]
                                  + ") "
                                  + " LZ game #"
                                  + counter
                                  + ": added branch at move "
                                  + branch.move
                              );
                          }
                        );

                        set.requests = [];
                        pending_selfplays.unshift(set);
                      }
                    })
                    .catch(() => {
                      console.log(
                        req.ip
                          + " ("
                          + req.headers["x-real-ip"]
                          + ") "
                          + " LZ game #"
                          + counter
                          + ": ERROR RETRIEVING SELFPLAY REQUEST"
                      );
                    });
                }
              }
            });
          }
        });
      }
    });
  }
});

app.get(
  "/matches",
  asyncMiddleware(async(req, res) => {
    const pug_data = {
      matches: await dbutils.get_matches_from_cache(db)
    };

    res.render("matches", pug_data);
  })
);

app.get(
  "/matches-all",
  asyncMiddleware(async(req, res) => {
    const pug_data = {
      matches: await dbutils.get_matches_from_db(db, { limit: 1000000 })
    };

    res.render("matches-all", pug_data);
  })
);

app.get(
  "/analyze/:hash(\\w+)",
  // eslint-disable-next-line no-unused-vars
  asyncMiddleware(async(req, res, next) => {
    const game = await db
      .collection("games")
      .findOne({ sgfhash: req.params.hash }, { sgf: true });
    if (!game) {
      return res.status(404).render("404");
    }
    const result = analyze_sgf(game.sgf);
    res.send(result);
  })
);

app.get(
  "/network-profiles",
  asyncMiddleware(async(req, res) => {
    const networks = await db
      .collection("networks")
      .find({
        hash: { $not: { $in: ELF_NETWORKS } },
        $or: [{ game_count: { $gt: 0 } }, { hash: get_best_network_hash() }]
      })
      .sort({ _id: -1 })
      .toArray();

    const pug_data = { networks, menu: "network-profiles" };

    pug_data.networks.forEach(network => {
      network.time = network._id.getTimestamp().getTime();
    });

    res.render("networks/index", pug_data);
  })
);

app.get(
  "/network-profiles/:hash(\\w+)",
  asyncMiddleware(async(req, res) => {
    const network = await db
      .collection("networks")
      .findOne({ hash: req.params.hash });

    if (!network) {
      return res.status(404).render("404");
    }

    // If it's one of the best network, then find it's #
    if (
      (network.game_count > 0 || network.hash == get_best_network_hash())
      && !ELF_NETWORKS.includes(network.hash)
    ) {
      network.networkID = await db.collection("networks").count({
        _id: { $lt: network._id },
        game_count: { $gt: 0 },
        hash: { $not: { $in: ELF_NETWORKS } }
      });
    }

    // Prepare Avatar
    const avatar_folder = path.join(__dirname, "static", "networks");
    if (!(await fs.pathExists(avatar_folder))) {
      await fs.mkdirs(avatar_folder);
    }

    const avatar_path = path.join(avatar_folder, network.hash + ".png");
    if (!fs.pathExistsSync(avatar_path)) {
      const retricon = require("retricon-without-canvas");

      await new Promise((resolve, reject) => {
        // GitHub style
        retricon(network.hash, {
          pixelSize: 70,
          imagePadding: 35,
          bgColor: "#F0F0F0"
        })
          .pngStream()
          .pipe(fs.createWriteStream(avatar_path))
          .on("finish", resolve)
          .on("error", reject);
      });
    }

    const pug_data = {
      network,
      http_host: req.protocol + "://" + req.get("host"),
      // Have to fetch from db since we only cache 100 recent matches
      matches: await dbutils.get_matches_from_db(db, { network: network.hash }),
      menu: "network-profiles"
    };

    res.render("networks/profile", pug_data);
  })
);

app.get(
  "/rss",
  asyncMiddleware(async(req, res) => {
    const rss_path = path.join(__dirname, "static", "rss.xml");
    const best_network_path = path.join(
      __dirname,
      "network",
      "best-network.gz"
    );
    let should_generate = true;
    const http_host = req.protocol + "://" + req.get("host");

    const rss_exists = await fs.pathExists(rss_path);

    if (rss_exists) {
      const best_network_mtimeMs = (await fs.stat(best_network_path)).mtimeMs;
      const rss_mtimeMs = (await fs.stat(rss_path)).mtimeMs;

      // We have new network promoted since rss last generated
      should_generate = best_network_mtimeMs > rss_mtimeMs;
    }

    if (should_generate || req.query.force) {
      const hash = await get_best_network_hash();
      const networks = await db
        .collection("networks")
        .find({
          $or: [{ game_count: { $gt: 0 } }, { hash }],
          hash: { $not: { $in: ELF_NETWORKS } }
        })
        .sort({ _id: 1 })
        .toArray();

      const rss_xml = new rss_generator().generate(networks, http_host);

      await fs.writeFile(rss_path, rss_xml);
    }

    res.setHeader("Content-Type", "application/rss+xml");
    res.sendFile(rss_path);
  })
);

app.get(
  "/home",
  asyncMiddleware(async(req, res) => {
    const client_list_24hr = await cacheIP24hr.wrap("IP24hr", "5m", () => Promise.resolve(
        db.collection("games").distinct("ip", {
          _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
        })
      )
    );

    const client_list_1hr = await cacheIP1hr.wrap("IP1hr", "30s", () => Promise.resolve(
        db.collection("games").distinct("ip", {
          _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) }
        })
      )
    );

    const selfplay_24hr = await db
      .collection("games")
      .find({
        _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
      })
      .count();

    const selfplay_1hr = await db
      .collection("games")
      .find({ _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) } })
      .count();

    const match_total = await db
      .collection("match_games")
      .find()
      .count();

    const match_24hr = await db
      .collection("match_games")
      .find({
        _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
      })
      .count();

    const match_1hr = await db
      .collection("match_games")
      .find({ _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) } })
      .count();

    const pug_data = {
      matches: await dbutils.get_matches_from_cache(db, 10),
      stats: {
        client_24hr: client_list_24hr.length,
        client_1hr: client_list_1hr.length,
        selfplay_total: counter,
        selfplay_24hr,
        selfplay_1hr,
        selfplay_elf: elf_counter,
        match_total,
        match_24hr,
        match_1hr
      }
    };

    res.render("index", pug_data);
  })
);

app.get(
  "/",
  asyncMiddleware(async(req, res) => {
    const client_list_24hr = await cacheIP24hr.wrap("IP24hr", "5m", () => Promise.resolve(
        db.collection("games").distinct("ip", {
          _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
        })
      )
    );

    const client_list_1hr = await cacheIP1hr.wrap("IP1hr", "30s", () => Promise.resolve(
        db.collection("games").distinct("ip", {
          _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) }
        })
      )
    );

    const selfplay_24hr = await db
      .collection("games")
      .find({
        _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
      })
      .count();

    const selfplay_1hr = await db
      .collection("games")
      .find({ _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) } })
      .count();

    const match_total = await db
      .collection("match_games")
      .find()
      .count();

    const match_24hr = await db
      .collection("match_games")
      .find({
        _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60 * 24) }
      })
      .count();

    const match_1hr = await db
      .collection("match_games")
      .find({ _id: { $gt: objectIdFromDate(Date.now() - 1000 * 60 * 60) } })
      .count();

    const pug_data = {
      matches: await dbutils.get_matches_from_cache(db, 10),
      stats: {
        client_24hr: client_list_24hr.length,
        client_1hr: client_list_1hr.length,
        selfplay_total: counter,
        selfplay_24hr,
        selfplay_1hr,
        selfplay_elf: elf_counter,
        match_total,
        match_24hr,
        match_1hr
      }
    };

    res.render("index", pug_data);
  })
);

/**
 * Determine which special selfplay should be scheduled.
 *
 * @param req {object} Express request
 * @param now {int} Timestamp right now
 * @returns {bool|object} False if no selfplay to schedule; otherwise, selfplay object
 */
function shouldScheduleSelfplay(req, now) {
  if (!(pending_selfplays.length && req.params.autogtp != 0)) return false;

  let i = pending_selfplays.length;
  while (--i >= 0) {
    const selfplay = pending_selfplays[i];
    const deleted = selfplay.requests.filter(
      e => e.timestamp < now - SELFPLAY_EXPIRE_TIME
    ).length;
    selfplay.requests.splice(0, deleted);
    const requested = selfplay.requests.length;
    if (selfplay.number_to_play > selfplay.game_count + requested)
      return selfplay;
  }
  return false;
}

/**
 * Determine if a match should be scheduled for a given request.
 *
 * @param req {object} Express request
 * @param now {int} Timestamp right now
 * @returns {bool|object} False if no match to schedule; otherwise, match object
 */
function shouldScheduleMatch(req, now) {
  if (
    !(
      pending_matches.length
      && req.params.autogtp != 0
      && (schedule_matches_to_all || fastClientsMap.get(req.ip))
    )
  ) {
    return false;
  }

  // Find the first match this client can play
  let match;
  let i = pending_matches.length;
  while (--i >= 0) {
    match = pending_matches[i];
    break;
  }

  // Don't schedule if we ran out of potential matches for this client
  if (i < 0) return false;

  const deleted = match.requests.filter(
    e => e.timestamp < now - MATCH_EXPIRE_TIME
  ).length;
  const oldest = (match.requests.length > 0
    ? (now - match.requests[0].timestamp) / 1000 / 60
    : 0
  ).toFixed(2);
  match.requests.splice(0, deleted);
  const requested = match.requests.length;
  const needed = how_many_games_to_queue(
    match.number_to_play,
    match.network1_wins,
    match.network1_losses,
    PESSIMISTIC_RATE,
    bestRatings.has(match.network1),
    no_early_fail
  );
  const result = needed > requested;
  console.log(
    `Need ${needed} match games. Requested ${requested}, deleted ${deleted}. Oldest ${oldest}m ago. Will schedule ${
      result ? "match" : "selfplay"
    }.`
  );

  return result && match;
}

/**
 * Get a self-play or match task depending on various client versions.
 * E.g., /get-task/0, /get-task/16, /get-task/0/0.14, /get-task/16/0.14
 */
async function get_task(req, res) {
  const required_client_version = String(16);
  const required_leelaz_version = String("0.17");

  // Pulling this now because if I wait inside the network2==null test, possible race condition if another get-task pops end of array?
  //
  const best_network_hash = await get_best_network_hash();
  const now = Date.now();
  const random_seed = make_seed(now / 1000).toString();

  // Track match assignments as they go out, so we don't send out too many. If more needed request them, otherwise selfplay.
  //
  const match = shouldScheduleMatch(req, now);
  if (match) {
    const task = {
      cmd: "match",
      required_client_version,
      minimum_autogtp_version: required_client_version,
      random_seed,
      minimum_leelaz_version: required_leelaz_version
    };

    if (match.options.visits) match.options.playouts = "0";

    task.options = match.options;
    task.options_hash = match.options_hash;

    if (match.network2 == null) {
      match.network2 = best_network_hash;

      db.collection("matches").updateOne(
        {
          network1: match.network1,
          network2: null,
          options_hash: match.options_hash
        },
        { $set: { network2: best_network_hash } },
        {},
        err => {
          if (err) {
            console.log("ERROR: /get-task setting network2: " + err);
            res.send("ERROR: /get-task setting network2: " + err);
            return;
          }
          dbutils.clear_matches_cache();
          console.log(
            "Match " + match._id + " set network2 to best: " + match.network2
          );
        }
      );
    }

    match.game_color = !match.game_color;

    if (match.game_color) {
      task.white_hash = match.network1;
      task.black_hash = match.network2;
    } else {
      task.white_hash = match.network2;
      task.black_hash = match.network1;
    }

    add_match_verification(task);
    await add_gzip_hash(task);
    res.send(JSON.stringify(task));

    match.requests.push({ timestamp: now, seed: random_seed });

    if (match.game_count >= match.number_to_play) pending_matches.pop();

    console.log(
      `${req.ip} (${
        req.headers["x-real-ip"]
      }) got task: match ${match.network1.slice(
        0,
        8
      )} vs ${match.network2.slice(0, 8)} ${match.game_count
        + match.requests.length} of ${match.number_to_play} ${JSON.stringify(
        task
      )}`
    );
    //    } else if ( req.params.autogtp==1 && Math.random() > .2 ) {
    //        const task = { "cmd": "wait", "minutes": "5" };
    //
    //        res.send(JSON.stringify(task));
    //
    //        console.log(req.ip + " (" + req.headers['x-real-ip'] + ") " + " got task: wait");
  } else {
    const self_play = shouldScheduleSelfplay(req, now);

    // {"cmd": "selfplay", "hash": "xxx", "playouts": 1000, "resignation_percent": 3.0}
    const task
      = !self_play && disable_default_selfplay
        ? { cmd: "wait", minutes: "5" }
        : {
            cmd: "selfplay",
            hash: "",
            required_client_version,
            minimum_autogtp_version: required_client_version,
            random_seed,
            minimum_leelaz_version: required_leelaz_version
          };

    //var options = {"playouts": "1600", "resignation_percent": "10", "noise": "true", "randomcnt": "30"};
    const options = {
      playouts: "0",
      visits: String(default_visits + 1),
      resignation_percent: String(default_resignation_percent),
      noise: "true",
      randomcnt: String(default_randomcnt),
      komi: String(default_komi),
      noise_value: String(default_noise_value),
      lambda: String(default_lambda),
      other_options: String(default_other_options_selfplay),
      dumbpass: String(config.default_dumbpass)
    };

    if (self_play) {
      console.log("Ayasii -> " + String(self_play.komi));
      options.komi = String(self_play.komi);
      // options.komi = String(default_komi);
      options.noise_value = String(self_play.noise_value);
      options.lambda = String(self_play.lambda);
      if ("dumbpass" in self_play)
        options.dumbpass = String(self_play.dumbpass);
      options.visits = String(self_play.visits);
      options.resignation_percent = String(self_play.resignation_percent);
      // options.other_options = String(self_play.other_options);
      // if (self_play.noise) options.noise = String(self_play.noise);
      options.noise = "true";
      task.hash = String(self_play.networkhash);
      task.selfplay_id = String(self_play._id);
      if (self_play.sgfhash) {
        task.sgfhash = String(self_play.sgfhash);
        task.movescount = String(self_play.movescount);
      }
      self_play.requests.push({ timestamp: now, seed: random_seed });
      if (Math.random() < self_play.no_resignation_probability)
        options.resignation_percent = "0";
    } else if (!disable_default_selfplay || req.params.autogtp == 0) {
      task.hash = best_network_hash;
      if (Math.random() < default_no_resignation_probability)
        options.resignation_percent = "0";
    }

    // For now, have newer autogtp and leelaz play some self-play with
    // Facebook's ELF Open Go network, which uses network version 2.
    //if ((req.params.autogtp >= 16 || req.params.leelaz >= 0.14) && Math.random() < 0.25) {
    //    task.hash = ELF_NETWORKS[1];
    //    options.resignation_percent = "5";
    //}

    //task.options_hash = checksum("" + options.playouts + options.resignation_percent + options.noise + options.randomcnt).slice(0,6);
    if (task.cmd != "wait") {
      task.options_hash = get_options_hash(options);
      task.options = options;
    }
    await add_gzip_hash(task);
    res.send(JSON.stringify(task));

    console.log(
      `${req.ip} (${
        req.headers["x-real-ip"]
      }) got task: selfplay ${JSON.stringify(task)}`
    );
  }
}

// GET version of get-task
app.get(
  "/get-task/:autogtp(\\d+)(?:/:leelaz([.\\d]+)?)",
  asyncMiddleware(async(req, res) => {
    get_task(req, res);
  })
);

// POST version of get-task with authentication
app.post(
  "/get-task/:autogtp(\\d+)(?:/:leelaz([.\\d]+)?)",
  asyncMiddleware(async(req, res) => {
    const user_name = validate_user(
      req.body.username,
      req.body.key
    );
    if (user_name === false) {
      console.log(`${req.ip} (${req.headers["x-real-ip"]}) /get-task: invalid authentication for "${req.body.username}"`);
      return res.status(400).send("Invalid authentication");
    } else get_task(req, res);
  })
);

app.post(
  "/request-selfplay",
  // eslint-disable-next-line no-unused-vars
  asyncMiddleware(async(req, res, next) => {
    const logAndFail = msg => {
      console.log(
        `${req.ip} (${req.headers["x-real-ip"]}) /request-selfplay: ${msg}`
      );
      console.log(
        `files: ${JSON.stringify(
          Object.keys(req.files || {})
        )}, body: ${JSON.stringify(req.body)}`
      );
      return res.status(400).send(msg + "\n");
    };

    const best_network_hash = await get_best_network_hash();

    if (!req.body.key || req.body.key != auth_key) {
      console.log(
        "AUTH FAIL: '"
          + String(req.body.key)
          + "' VS '"
          + String(auth_key)
          + "'"
      );

      return res.status(400).send("Incorrect key provided.");
    }

    if (req.body.sgfhash && req.body.networkhash)
      return logAndFail("Both parameters sgfhash and networkhash are provided");
    if (!req.body.priority) return logAndFail("No priority provided");

    const set = {
      priority: parseFloat(req.body.priority),
      noise_value: req.body.noise_value
        ? parseFloat(req.body.noise_value)
        : default_noise_value,
      // noise: req.body.noise ? req.body.noise.toLowerCase() == "true" : "true",
      noise: "true",
      komi: req.body.komi ? parseFloat(req.body.komi) : default_komi,
      // komi: default_komi,
      lambda: req.body.lambda ? parseFloat(req.body.lambda) : default_lambda,
      dumbpass:
        "dumbpass" in req.body
          ? req.body.dumbpass.toLowerCase() === "true"
          : config.default_dumbpass,
      acceleration_endgame:
        req.body.acceleration_endgame ? req.body.acceleration_endgame.toLowerCase() == "true" : "true",
      other_options:
        "other_options" in req.body
          ? String(req.body.other_options)
          : default_other_options_selfplay,
      number_to_play: req.body.number_to_play
        ? parseInt(req.body.number_to_play)
        : 1,
      visits: req.body.visits ? parseInt(req.body.visits) : default_visits,
      resignation_percent: req.body.resignation_percent
        ? parseFloat(req.body.resignation_percent)
        : default_resignation_percent,
      no_resignation_probability: req.body.no_resignation_probability
        ? parseFloat(req.body.no_resignation_probability)
        : default_no_resignation_probability,
      game_count: 0,
      ip: req.headers["x-real-ip"] || req.ip
    };

    if (req.body.sgfhash) {
      if (!req.body.movescount)
        return logAndFail(
          "No movescount provided, although sgfhash is provided"
        );
      const selfplay = await db
        .collection("games")
        .findOne({ sgfhash: req.body.sgfhash }, { _id: 1, networkhash: 1 });
      if (!selfplay)
        return logAndFail(
          "No selfplay was found with hash " + req.body.sgfhash
        );
      set.networkhash = selfplay.networkhash;
      set.sgfhash = req.body.sgfhash;
      set.movescount = parseInt(req.body.movescount);
    } else if (req.body.networkhash) {
      const network = await db
        .collection("networks")
        .findOne({ hash: req.body.networkhash }, { _id: 1 });
      if (!network)
        return logAndFail(
          "No network was found with hash " + req.body.networkhash
        );
      set.networkhash = req.body.networkhash;
    } else {
      set.networkhash = best_network_hash;
    }

    await db.collection("self_plays").insertOne(set);
    if (set.networkhash == best_network_hash) {
      set.requests = [];
      pending_selfplays.unshift(set);
    }

    console.log(
      req.ip + " (" + req.headers["x-real-ip"] + ") " + " uploaded self-play"
    );
    res.send(
      "Self-play request for game "
        + set.sgfhash
        + " network "
        + set.networkhash
        + " stored in database.\n"
    );
  })
);

app.get("/view/:hash(\\w+).sgf", (req, res) => {
  db.collection("games")
    .findOne({ sgfhash: req.params.hash }, { _id: 0, sgf: 1 })
    .then(({ sgf }) => {
      sgf = sgf.replace(/(\n|\r)+/g, "");

      res.setHeader(
        "Content-Disposition",
        "attachment; filename=\"" + req.params.hash + ".sgf\""
      );
      res.setHeader("Content-Type", "application/x-go-sgf");
      res.send(sgf);
    })
    .catch(() => {
      res.send("No self-play was found with hash " + req.params.hash);
    });
});

app.get("/view/:hash(\\w+)", (req, res) => {
  db.collection("games")
    .findOne({ sgfhash: req.params.hash }, { _id: 0, sgf: 1 })
    .then(({ sgf }) => {
      sgf = sgf.replace(/(\n|\r)+/g, "");

      switch (req.query.viewer) {
        case "eidogo":
          res.render("eidogo", {
            title: "View training game " + req.params.hash,
            sgf
          });
          break;
        case "wgo":
          res.render("wgo", {
            title: "View training game " + req.params.hash,
            sgf
          });
          break;
        default:
          res.render("eidogo", {
            title: "View training game " + req.params.hash,
            sgf
          });
      }
    })
    .catch(() => {
      res.send("No selfplay game was found with hash " + req.params.hash);
    });
});

app.get("/self-plays", (req, res) => {
  db.collection("games")
    .find({}, { data: 0 })
    .sort({ _id: -1 })
    .limit(5000)
    .toArray()
    .then(list => {
      process_games_list(list, req.ip);
      // render pug view self-plays
      res.render("self-plays", { data: list });
    })
    .catch(() => {
      res.send("Failed to get recent self-play games");
    });
});

app.get("/match-games/:matchid(\\w+)", (req, res) => {
  if (!req.params.matchid) {
    res.send("matchid missing");
    return;
  }

  db.collection("matches")
    .findOne({ _id: new ObjectId(req.params.matchid) })
    .then(match => {
      db.collection("match_games")
        .aggregate([
          {
            $match: {
              $or: [
                {
                  winnerhash: match.network1,
                  loserhash: match.network2,
                  options_hash: match.options_hash
                },
                {
                  winnerhash: match.network2,
                  loserhash: match.network1,
                  options_hash: match.options_hash
                }
              ]
            }
          },
          { $sort: { _id: 1 } }
        ])
        .toArray()
        .then(list => {
          process_games_list(list, req.ip, match.network1);
          // render pug view match-games
          res.render("match-games", { data: list });
        })
        .catch(() => {
          res.send("No matches found for match " + req.params.matchid);
        });
    })
    .catch(() => {
      res.send("No match found for id " + req.params.hash);
    });
});

app.get("/viewmatch/:hash(\\w+).sgf", (req, res) => {
  db.collection("match_games")
    .findOne({ sgfhash: req.params.hash }, { _id: 0, sgf: 1 })
    .then(({ sgf }) => {
      sgf = sgf.replace(/(\n|\r)+/g, "");

      res.setHeader(
        "Content-Disposition",
        "attachment; filename=\"" + req.params.hash + ".sgf\""
      );
      res.setHeader("Content-Type", "application/x-go-sgf");
      res.send(sgf);
    })
    .catch(() => {
      res.send("No match was found with hash " + req.params.hash);
    });
});

app.get("/viewmatch/:hash(\\w+)", (req, res) => {
  db.collection("match_games")
    .findOne({ sgfhash: req.params.hash }, { _id: 0, sgf: 1 })
    .then(({ sgf }) => {
      sgf = sgf.replace(/(\n|\r)+/g, "");

      switch (req.query.viewer) {
        case "eidogo":
          res.render("eidogo", {
            title: "View training game " + req.params.hash,
            sgf
          });
          break;
        case "wgo":
          res.render("wgo", { title: "View match " + req.params.hash, sgf });
          break;
        default:
          res.render("eidogo", {
            title: "View training game " + req.params.hash,
            sgf
          });
      }
    })
    .catch(() => {
      res.send("No match was found with hash " + req.params.hash);
    });
});

app.get(
  "/data/elograph.json",
  asyncMiddleware(async(req, res) => {
    // cache in `cachematches`, so when new match result is uploaded, it gets cleared as well
    const json = await cachematches.wrap("elograph", "1d", async() => {
      console.log(
        "fetching data for elograph.json, should be called once per day or when `cachematches` is cleared"
      );

      const cursor = db
        .collection("networks")
        .aggregate([{ $group: { _id: 1, count: { $sum: "$game_count" } } }]);
      const totalgames = await cursor.next();

      return Promise.all([
        db
          .collection("networks")
          .find()
          .sort({ _id: -1 })
          .toArray(),
        db
          .collection("matches")
          .aggregate([
            {
              $lookup: {
                localField: "network2",
                from: "networks",
                foreignField: "hash",
                as: "merged"
              }
            },
            { $unwind: "$merged" },
            { $sort: { "merged._id": 1 } }
          ])
          .toArray()
      ])
        .then(dataArray => {
          // initialize mapping of best networks to Elo rating cached globally
          bestRatings = new Map();

          // prepare networks
          const networks = dataArray[0].map(item => {
            totalgames.count -= item.game_count || 0;

            // The ELF network has games but is not actually best
            const best
              = item.game_count
              && !ELF_NETWORKS.some(n => n.startsWith(item.hash));
            if (best) bestRatings.set(item.hash, 0);

            return {
              hash: item.hash,
              game_count: item.game_count,
              net:
                item.training_count === 0 || item.training_count
                  ? item.training_count
                  : totalgames.count, // mycount
              best
            };
          });

          // prepare ratingsMap
          const ratingsMap = new Map();
          dataArray[1].forEach(match => {
            const network2_rating = ratingsMap.get(match.network2)
              ? ratingsMap.get(match.network2).rating
              : 0;
            let sprt;
            let elo;

            // TODO If no Elo info, make rating -1 for graph to just hide it instead of assuming same Elo as network 2.
            //
            if (match.network1_wins > 0 && match.network1_losses > 0) {
              elo = CalculateEloFromPercent(
                match.network1_wins / match.game_count
              );
            } else {
              let fakecount = match.game_count;
              let fakewins = match.network1_wins;

              if (fakewins == 0) {
                fakewins++;
                fakecount++;
              }

              if (match.network1_losses == 0) {
                fakecount++;
              }

              elo = CalculateEloFromPercent(fakewins / fakecount);
            }

            // Hide *-vs-ELF test matches as there's no meaningful Elo reference
            if (ELF_NETWORKS.includes(match.network2)) {
              elo = 0;
            }

            const isBest = bestRatings.has(match.network1);
            switch (
              isBest || SPRT(match.network1_wins, match.network1_losses)
            ) {
              case false:
                sprt = "FAIL";
                break;

              case true:
                sprt = "PASS";
                break;

              default:
                sprt = "???";
            }

            // Force the match to show up as a test instead of the usual SPRT
            if (match.is_test) {
              sprt = "TEST";
            }

            // Save ratings of best networks
            const rating = elo + network2_rating;
            if (isBest && !match.is_test)
              bestRatings.set(match.network1, rating);

            // Use opponent's net for ELF as its training_count is arbitrary
            const net
              = ELF_NETWORKS.includes(match.network1)
              && match.merged.training_count;

            // Chain together previous infos if we have any
            const previous = ratingsMap.get(match.network1);
            const info = { net, previous, rating, sprt };
            ratingsMap.set(match.network1, info);
          });

          // Matches table uses data from bestRatings, so allow it to refresh
          cachematches.del("matches", () => console.log("Cleared match table cache.")
          );

          // prepare json result
          const json = [];
          const addNetworkRating = (
            item,
            info = { rating: 0, sprt: "???" }
          ) => {
            const rating = Math.max(0, Math.round(info.rating));
            json.push({
              rating,
              net: Math.max(
                0.0,
                Number((info.net || item.net) + rating / 100000)
              ),
              sprt: info.sprt,
              hash: item.hash.slice(0, 6),
              best: item.best && info.sprt !== "TEST"
            });

            // Add additional result for multiple matches
            if (info.previous) addNetworkRating(item, info.previous);
          };
          networks.forEach(item => addNetworkRating(item, ratingsMap.get(item.hash))
          );

          // shortcut for sending json result using `JSON.stringify`
          // and set `Content-Type: application/json`
          return json;
        })
        .catch(err => {
          console.log("ERROR data/elograph.json: " + err);
          res.send("ERROR data/elograph.json: " + err);
        });
    });

    res.json(json);
  })
);

/*
app.get("/opening/:start(\\w+)?", asyncMiddleware(async(req, res) => {
    let start = req.params.start;
    const files = {
        44: "top10-Q16.json",
        43: "top10-R16.json",
        33: "top10-R17.json"
    };

    if (!(start in files))
        start = "44";

    const top10 = JSON.parse(fs.readFileSync(path.join(__dirname, "static", files[start])));

    return res.render("opening", { top10, start, menu: "opening" });
}));
*/

app.get(
  "/admin/access-logs",
  asyncMiddleware(async(req, res) => {
    const url = req.query.url;
    res.render("admin/access-logs", { url });
  })
);

// Data APIs
app.get(
  "/api/access-logs",
  asyncMiddleware(async(req, res) => {
    const url = req.query.url;
    const logs = await dbutils.get_access_logs(db, url);
    res.setHeader("Content-Type", "application/json");
    res.send(JSON.stringify(logs));
  })
);

app.get(
  "/debug/exception",
  asyncMiddleware(async() => {
    throw new Error("handler error test" + Date.now());
  })
);

app.get("/debug/promise", (req, res) => {
  const foo = async() => Promise.reject("Unhandled Exception " + Date.now());
  foo();
  res.send("ok");
});

app.post(
  "/user-request",
  asyncMiddleware(async(req, res) => {
    const logAndFail = msg => {
      console.log(
        `${req.ip} (${req.headers["x-real-ip"]}) /admin/user-request: ${msg}`
      );
      return res.status(400).send(msg);
    };

    if (!req.body.username) return logAndFail("Computername not provided.");
    if (!req.body.email) return logAndFail("Email not provided.");
    if (!email_validator.validate(req.body.email))
      return logAndFail("Email format is not valid.");

    if (!req.body.password) return logAndFail("No password provided.");
    if (!req.body.password2)
      return logAndFail("No confirmation password provided.");
    if (req.body.password != req.body.password2)
      return logAndFail("Password do not matches.");
    if (req.body.password.length > 254) return logAndFail("Password too long.");

    const username = req.body.username;
    const email = req.body.email;

    const hash = crypto.createHash("sha256");
    hash.update(req.body.password);
    const password = hash.digest("hex");

    if (await db.collection("users").findOne({ username }))
      return logAndFail("User with given computername already exists.");

    const token = crypto
      .randomBytes(48)
      .toString("base64")
      .replace(/\//g, "_")
      .replace(/\+/g, "-");
    const insert = await db.collection("users").insertOne({
      username,
      email,
      password,
      token,
      active: false
    });

    if (!insert) return logAndFail("Error adding user to db.");

    const transporter = nodemailer.createTransport(config.mail_transport);

    // const url = config.base_url + "bsk" + instance_number;

    const mail_options = {
      from: config.mail_from,
      to: email,
      cc: config.mail_from,
      subject: "Request for BSK user account",
      text: `Please confirm your email for computer ${username} connecting to ${config.base_url}/user-confirm/${encodeURIComponent(
        username
      )}/${token}`
    };

    const email_info = await transporter.sendMail(mail_options);
    if (!email_info) return logAndFail("Error sending email.");

    console.log(
      `${req.ip} (${
        req.headers["x-real-ip"]
      }) request new computer ${username} for address ${email}.`
    );
    res.send(
      "OK, an email has been sent to your address. You can now close this window."
    );
  })
);

app.get(
  "/user-request",
  asyncMiddleware(async(req, res) => {
    const pug_data = {};
    res.render("user-request", pug_data);
  })
);

app.get(
  "/user-confirm/:username/:token",
  asyncMiddleware(async(req, res) => {
    const logAndFail = msg => {
      console.log(
        `${req.ip} (${req.headers["x-real-ip"]}) /admin/user-confirm: ${msg}`
      );
      return res.status(400).send(msg);
    };

    const username = req.params.username;
    const token = req.params.token;

    const command_result = await db
      .collection("users")
      .findOneAndUpdate(
        { username, token },
        { $set: { active: true }, $unset: { token: "" } }
      );
    const user = command_result.value;

    if (!user) return logAndFail("Wrong credentials.");
    else {
      current_users.set(user.username, user.password);
      console.log(
        `${req.ip} (${req.headers["x-real-ip"]}) confirmed user ${username}.`
      );
      return res.send(
        `Congratulations! Your account for computer ${username} has been created. You can now close this window.`
      );
    }
  })
);

// Catch all, return 404 page not found
app.get(
  "*",
  asyncMiddleware(async(req, res) => res.status(404).render("404"))
);

if (config.RAVEN_DSN) {
  app.use(Raven.errorHandler());
}
