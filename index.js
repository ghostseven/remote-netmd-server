"use strict";

import express from 'express';
import http from 'http';
import https from 'https';
import expressWs from 'express-ws';
import {
    WebUSB
} from 'usb';
import yargs from 'yargs';
import fs from 'fs';
import { createRequire } from 'module';
import { Worker } from 'worker_threads';
import {
    hideBin
} from 'yargs/helpers';
import {
    sanitizeFullWidthTitle,
    sanitizeHalfWidthTitle
} from 'netmd-js/dist/utils.js';
import {
    MDTrack,
    getDeviceStatus,
    Encoding,
    listContent,
    openNewDevice,
    renameDisc,
    DevicesIds,
    rewriteDiscGroups,
    prepareDownload,
    MDSession,
    Wireformat,
    DiscFormat,
    DiscFlag,
    upload as readTrackFromDevice,
    formatToHiMD,
    readUTOCSector,
    writeUTOCSector,
    getDescriptiveDeviceCode,
    cleanRead,
    MemoryType,
} from 'netmd-js';
import { makeGetAsyncPacketIteratorOnWorkerThread } from 'netmd-js/dist/node-encrypt-worker.js';
import {
    ExploitStateManager,
    isCompatible,
    getBestSuited,
    AtracRecovery,
    CachedSectorControlDownload,
    FirmwareDumper,
    ForceTOCEdit,
    Tetris,
    PCMFasterUpload,
    SPUpload,
    HiMDUSBClassOverride,
    MonoSPUpload,
    DisableDiscDetection,
    EnterServiceMode,
    ConsoleLogger,
} from 'netmd-exploits';
import {
    Mutex
} from 'async-mutex';

// Web Minidisc Pro only talks to servers reporting this version.
const PROTOCOL_VERSION = '1.0';
// Bumped whenever endpoints are added. Clients announce theirs with `/?client=N`,
// so capabilities that need newer client code are only offered to clients that have it.
const API_REVISION = 3;

const require = createRequire(import.meta.url);
const encryptWorkerPath = require.resolve('netmd-js/dist/node-encrypt-worker.js');

// Compatibility methods. Do NOT use these unless absolutely necessary!!
// These have to match Web Minidisc Pro's `src/services/interfaces/netmd.ts`.
export function convertDiscToWMD(source){
    return {
        ...source,
        left: Math.ceil(source.left / 512),
        total: Math.ceil(source.total / 512),
        groups: source.groups.map(convertGroupToWMD),
    };
}

export function convertDiscToNJS(source){
    return {
        ...source,
        left: source.left * 512,
        total: source.total * 512,
        groups: source.groups.map(convertGroupToNJS),
    };
}

export function convertGroupToWMD(source){
    return {
        ...source,
        tracks: source.tracks.map(convertTrackToWMD)
    };
}

export function convertGroupToNJS(source){
    return {
        ...source,
        tracks: source.tracks.map(convertTrackToNJS),
    };
}

export function convertTrackToWMD(source){
    return ({
        ...source,
        duration: Math.ceil(source.duration / 512),
        encoding: ({
            [Encoding.sp]: source.channel === 1 ? { codec: 'SPM', bitrate: 146 } : { codec: 'SPS', bitrate: 292 },
            [Encoding.lp2]: { codec: 'AT3', bitrate: 132 },
            [Encoding.lp4]: { codec: 'AT3', bitrate: 66 },
        })[source.encoding],
    });
}

export function convertTrackToNJS(source){
    return {
        ...source,
        duration: source.duration * 512,
        encoding: source.encoding.codec.startsWith('SP') ? Encoding.sp : source.encoding.bitrate === 132 ? Encoding.lp2 : Encoding.lp4,
    }
}

function isSequential(numbers) {
    if (numbers.length === 0) return true;
    let last = numbers[0];
    for (let num of numbers) {
        if (num === last) {
            ++last;
        } else return false;
    }
    return true;
}

// Port of Web Minidisc Pro's `recomputeGroupsAfterTrackMove` (src/utils.ts).
// Pass -1 as `targetIndex` when deleting a track.
function recomputeGroupsAfterTrackMove(disc, trackIndex, targetIndex) {
    let offset = trackIndex > targetIndex ? 1 : -1;
    const deleteMode = targetIndex === -1;

    if (deleteMode) {
        offset = -1;
        targetIndex = disc.trackCount;
    }

    const boundsStart = Math.min(trackIndex, targetIndex);
    const boundsEnd = Math.max(trackIndex, targetIndex);

    const allTracks = disc.groups
        .map(n => n.tracks)
        .reduce((a, b) => a.concat(b), [])
        .sort((a, b) => a.index - b.index)
        .filter(n => !deleteMode || n.index !== trackIndex);

    const groupBoundaries = disc.groups
        .filter(n => n.title !== null)
        .map(group => ({
            name: group.title,
            fullWidthName: group.fullWidthTitle,
            start: group.tracks[0].index,
            end: group.tracks[0].index + group.tracks.length - 1,
        })); // Convert to a format better for shifting

    let anyChanges = false;

    for (const group of groupBoundaries) {
        if (group.start > boundsStart && group.start <= boundsEnd) {
            group.start += offset;
            anyChanges = true;
        }
        if (group.end >= boundsStart && group.end < boundsEnd) {
            group.end += offset;
            anyChanges = true;
        }
    }

    if (!anyChanges) return disc;

    const newDisc = { ...disc };

    // Convert back
    newDisc.groups = groupBoundaries
        .map(n => ({
            title: n.name,
            fullWidthTitle: n.fullWidthName,
            index: n.start,
            tracks: allTracks.slice(n.start, n.end + 1),
        }))
        .filter(n => n.tracks.length > 0);

    // Convert ungrouped tracks
    const allGrouped = newDisc.groups.map(n => n.tracks).reduce((a, b) => a.concat(b), []);
    const ungrouped = allTracks.filter(n => !allGrouped.includes(n));

    // Fix all the track indexes
    if (deleteMode) {
        for (let i = 0; i < allTracks.length; i++) {
            allTracks[i].index = i;
        }
    }

    if (ungrouped.length) newDisc.groups.unshift({ title: null, fullWidthTitle: null, index: 0, tracks: ungrouped });

    return newDisc;
}

const webusb = new WebUSB({
    allowedDevices: DevicesIds.map(({
        deviceId,
        vendorId
    }) => ({
        productId: deviceId,
        vendorId
    })),
    deviceTimeout: 1000000,
});
const mutex = new Mutex();

const netmdLogger = {
    debug: () => {},
    info: console.log,
    warn: console.log,
    error: console.log,
    child: () => netmdLogger,
};

let awaitingDeviceLockMutexRelease = null;
let device = null;
// The disc's contents, already converted to Web Minidisc Pro's format
let cachedContent = undefined;
// The factory (homebrew) mode state, created on the first factory request for the connected device
let factoryState = null;

async function getCachedContent() {
    if (!cachedContent) cachedContent = convertDiscToWMD(await listContent(device));
    return JSON.parse(JSON.stringify(cachedContent));
}

function flushCache() {
    cachedContent = undefined;
}

function sleep(ms) {
    return new Promise(resolve => {
        setTimeout(resolve, ms);
    });
}

function errorMessage(error) {
    return error instanceof Error ? error.message : String(error);
}

function fail(res, error) {
    try {
        res.json({
            ok: false,
            error: errorMessage(error),
        });
    } catch (err) {}
}

function success(res, value) {
    try {
        res.json(value !== undefined ? {
            ok: true,
            value
        } : {
            ok: true
        });
    } catch (err) {}
}

// Wraps a request handler, so that its result (or error) is always sent back to the client.
function handle(handler) {
    return async (req, res) => {
        try {
            success(res, await handler(req.query, req.body ?? {}));
        } catch (ex) {
            console.log(`Error while handling ${req.path}: ${errorMessage(ex)}`);
            fail(res, ex);
        }
    };
}

function intParameter(parameters, name) {
    const value = parseInt(parameters[name]);
    if (isNaN(value)) throw new Error(`Missing parameter: ${name}`);
    return value;
}

function stringParameter(parameters, name) {
    const value = parameters[name];
    if (value === undefined || value === null) throw new Error(`Missing parameter: ${name}`);
    return String(value);
}

async function getCapabilities(clientRevision) {
    // Mirrors NetMDUSBService.getServiceCapabilities() in Web Minidisc Pro.
    const capabilities = ['contentList', 'playbackControl', 'fullWidthSupport'];
    const isSony = device.netMd.getVendor() === 0x54c;
    const newClient = clientRevision >= 2;

    if (newClient && isSony && device.netMd.getProduct() === 0x0286) {
        // MZ-RH1
        capabilities.push('trackDownload');
    }
    if (isSony && await device.canEjectDisc()) {
        capabilities.push('discEject');
    }
    const deviceName = device.netMd.getDeviceName();
    if (clientRevision >= 3 && (
        (deviceName.includes('Sony') &&
            (deviceName.includes('MZ-N') || deviceName.includes('MZ-S1') || deviceName.includes('MZ-RH') || deviceName.includes('MZ-DH10P') || deviceName.includes('DS-HMD1'))) ||
        (deviceName.includes('Aiwa') && deviceName.includes('AM-NX')) ||
        deviceName.includes('PCGA-MDN1')
    )) {
        // Only Sony (and Aiwa since it's the same thing) portables have the factory mode.
        capabilities.push('factoryMode');
    }
    if (newClient && (deviceName.includes("MZ-RH") || deviceName.includes("MZ-NH") || deviceName.includes("CMT-AH10"))) {
        capabilities.push('himdFormat');
    }
    if (newClient && device.netMd.getDeviceFlags()?.nativeMonoUpload) {
        capabilities.push('nativeMonoUpload');
    }
    try {
        const flags = await device.getDiscFlags();
        if ((flags & DiscFlag.writeProtected) === 0) {
            capabilities.push('trackUpload', 'metadataEdit');
        }
    } catch (err) {}
    return capabilities;
}

// Enters the factory mode on first use. The state lives as long as the device stays connected.
async function getFactory() {
    if (!factoryState) {
        try {
            await device.stop();
        } catch (ex) {}
        const factory = await device.factory();
        const esm = await ExploitStateManager.create(device, factory, ConsoleLogger);
        factoryState = { factory, esm, atracDownloader: null, fasterTransferEnabled: false };
    }
    return factoryState;
}

// Mirrors NetMDFactoryUSBService.getExploitCapabilities() in Web Minidisc Pro.
// The names match its `ExploitCapability` enum.
function getExploitCapabilities(esm) {
    const capabilities = [];
    const bind = (exploit, name) => isCompatible(exploit, esm.device) && capabilities.push(name);
    bind(FirmwareDumper, 'readFirmware');
    bind(AtracRecovery, 'downloadAtrac');
    bind(Tetris, 'runTetris');
    bind(ForceTOCEdit, 'flushUTOC');
    bind(PCMFasterUpload, 'spUploadSpeedup');
    bind(SPUpload, 'uploadAtrac1');
    bind(HiMDUSBClassOverride, 'himdFullMode');
    bind(MonoSPUpload, 'uploadMonoSP');
    bind(DisableDiscDetection, 'disableDiscSwapDetection');
    bind(EnterServiceMode, 'enterServiceMode');
    if (!esm.device.isHimd) {
        // Non-HiMD devices can read the RAM using normal commands
        capabilities.push('readRam');
    }
    return capabilities;
}

async function main() {

    const args = yargs(hideBin(process.argv))
        .option("https", {
            type: "boolean",
            describe: "Use HTTPS instead of HTTP",
        })
        .option("httpsCert", {
            type: "string",
            describe: "The HTTPS certificate",
        })
        .option("httpsKey", {
            type: "string",
            describe: "The HTTPS key",
        })
        .option("port", {
            type: "number",
            describe: "The port on which to host",
        })
        .default("port", 11396)
        .default("https", true)
        .default("httpsCert", "cert.pem")
        .default("httpsKey", "key.pem")
        .help()
        .parse();

    const {
        port,
        https: useHttps,
        httpsCert,
        httpsKey
    } = args;
    // ********************** Express initialization *********************
    const app = express();
    const server = useHttps ? https.createServer({
        key: fs.readFileSync(httpsKey),
        cert: fs.readFileSync(httpsCert),
    }, app) : http.createServer(app);
    expressWs(app, server);
    app.use(express.json({ limit: '10mb' }));

    app.use((req, res, next) => {
        res.set("Access-Control-Allow-Origin", "*");
        res.set("Access-Control-Allow-Headers", "Content-Type");
        // Fliter out preflight requests
        if(req.method === "OPTIONS"){
            console.log(`Preflight request to ${req.url}`);
            if(req.header("Access-Control-Request-Private-Network") === "true"){
                res.header("Access-Control-Allow-Private-Network", "true");
            }
            res.status(204).send("");
            return;
        }
        next();
    });

    // Make sure there is no way to call two methods at the same time.
    app.use((req, res, next) => {
        if (awaitingDeviceLockMutexRelease || !device) {
            fail(res, "Not ready.");
            return;
        }
        console.log(`Called ${req.url}`);
        // The WebSocket endpoints take the lock themselves, for as long as the transfer runs
        if (req.path.endsWith("/.websocket")) {
            next();
            return;
        }
        mutex.acquire().then(release => {
            let released = false;
            const releaseOnce = () => {
                if (!released) {
                    released = true;
                    release();
                }
            };
            res.on('finish', releaseOnce);
            res.on('error', (e) => {
                console.log(`Error while handling: ${e}.`);
                releaseOnce();
            });
            res.on('close', releaseOnce);
            next();
        }).catch(ex => console.log(ex));
    });

    setup(app);

    // *********************** NetMD initialization **********************
    setTimeout(async function reloadDevices() {
        try{
            if (awaitingDeviceLockMutexRelease) {
                device = await openNewDevice(webusb, netmdLogger);
                if (device !== null) {
                    awaitingDeviceLockMutexRelease();
                    awaitingDeviceLockMutexRelease = null;
                    console.log(`Connected to ${device.netMd.getDeviceName()}. Application resumed.`);
                    factoryState = null;
                    flushCache();
                }
            }
        }catch(ex){
            console.log(ex);
        }
        setTimeout(reloadDevices, 1000);
    }, 1000);

    webusb.addEventListener("disconnect", () => {
        if(mutex.isLocked()){
            mutex.cancel();
            mutex.release();
        }
        device = null;
        factoryState = null;
        console.log("Device disconnected.");
        console.log("Awaiting new device...");
        flushCache();
        mutex.acquire().then(release => awaitingDeviceLockMutexRelease = release);
    });

    device = await openNewDevice(webusb, netmdLogger);

    if (device === null) {
        console.log("Error: No NetMD devices found.");
        console.log("Awaiting new device...");
        mutex.acquire().then(release => awaitingDeviceLockMutexRelease = release);
    } else {
        console.log(`Connected to ${device.netMd.getDeviceName()}`);
    }


    server.listen(port, () => console.log(`Started ${useHttps ? "https" : "http"} server on port ${port}.`));
}
main();

// Runs `handler` for a WebSocket transfer while holding the device lock.
// The lock is released and the socket closed when the handler finishes or fails.
function withLockedWebSocket(ws, handler) {
    mutex.acquire().then(async release => {
        let finished = false;
        const finish = () => {
            if (finished) return;
            finished = true;
            release();
        };
        ws.on('close', finish);
        ws.on('error', finish);
        try {
            await handler();
        } catch (ex) {
            console.log(ex);
            try {
                ws.send(JSON.stringify({ error: errorMessage(ex) }));
                ws.close();
            } catch (err) {}
        }
        finish();
    }).catch(e => console.log(e));
}

// Runs a factory mode WebSocket transfer. Besides the throttled progress messages,
// the handler can ask the client a question and wait for its answer, check whether
// the client cancelled, and collect binary data sent by the client (ended by `{ end: true }`).
// It returns `{ value, buffers }`: `value` is sent as `{ done: value, buffers: n }`,
// followed by each of the `n` buffers as its own binary message.
function factoryWebSocket(ws, handler) {
    const received = [];
    let resolveReceived, rejectReceived;
    const allReceived = new Promise((res, rej) => {
        resolveReceived = res;
        rejectReceived = rej;
    });
    allReceived.catch(() => {});
    let pendingAnswer = null;
    let cancelled = false;
    // A client that went away mid-transfer cancels it
    ws.on('close', () => {
        cancelled = true;
        rejectReceived(new Error("The client disconnected."));
        if (pendingAnswer) pendingAnswer('abort');
        pendingAnswer = null;
    });
    ws.on('message', message => {
        // Text messages are control messages, binary ones are data
        if (typeof message !== 'string') {
            received.push(new Uint8Array(message));
            return;
        }
        const json = JSON.parse(message);
        if (json.end) resolveReceived(received);
        if (json.cancel) cancelled = true;
        if ('answer' in json && pendingAnswer) {
            const resolve = pendingAnswer;
            pendingAnswer = null;
            resolve(json.answer);
        }
    });

    withLockedWebSocket(ws, async () => {
        let lastTime = 0;
        const context = {
            progress(data) {
                const newTime = new Date().getTime();
                if (newTime - lastTime > 100) {
                    ws.send(JSON.stringify({ progress: data }));
                    lastTime = newTime;
                }
            },
            ask(question) {
                return new Promise(res => {
                    pendingAnswer = res;
                    ws.send(JSON.stringify({ question }));
                });
            },
            isCancelled: () => cancelled,
            receiveData: () => allReceived,
        };
        const { value = null, buffers = [] } = (await handler(context)) ?? {};
        ws.send(JSON.stringify({ done: value, buffers: buffers.length }));
        for (const buffer of buffers) {
            ws.send(buffer);
        }
    });
}

function setup(app) {
    // ********************* NetMD <==> REST bridge **********************
    // Basic pages:
    app.get("/", handle(async ({ client }) => ({
        device: device.netMd.getDeviceName(),
        capabilities: await getCapabilities(parseInt(client) || 1),
        version: PROTOCOL_VERSION,
        apiRevision: API_REVISION,
    })));

    app.get('/deviceStatus', handle(async () => {
        const devStat = await getDeviceStatus(device);
        if(!devStat.discPresent) flushCache();
        return devStat;
    }));

    // The 'contentList' capability:

    app.get('/listContent', handle(async ({ flushCache: dropCache }) => {
        if (dropCache === 'true') flushCache();
        return await getCachedContent();
    }));

    app.get('/deviceName', handle(async () => device.netMd.getDeviceName()));

    app.get('/finalize', handle(async () => {
        await device.netMd.finalize();
        flushCache();
    }));

    // The 'metadataEdit' capability:

    app.get('/renameTrack', handle(async (parameters) => {
        const index = intParameter(parameters, 'index');
        const title = sanitizeHalfWidthTitle(stringParameter(parameters, 'title'));
        const { fullWidthTitle } = parameters;

        await device.setTrackTitle(index, title);
        if (fullWidthTitle !== undefined) {
            await device.setTrackTitle(index, sanitizeFullWidthTitle(fullWidthTitle), true);
        }
        flushCache();
    }));

    app.get('/renameDisc', handle(async (parameters) => {
        const title = stringParameter(parameters, 'title');
        await renameDisc(device, title, parameters.fullWidthTitle);
        flushCache();
    }));

    app.get('/renameGroup', handle(async (parameters) => {
        const groupIndex = intParameter(parameters, 'groupIndex');
        const title = stringParameter(parameters, 'title');
        const { fullWidthTitle } = parameters;

        const disc = await getCachedContent();
        const thisGroup = disc.groups.find(g => g.index === groupIndex);
        if (!thisGroup) {
            return;
        }

        thisGroup.title = title;
        if (fullWidthTitle !== undefined) {
            thisGroup.fullWidthTitle = fullWidthTitle;
        }
        flushCache();
        await rewriteDiscGroups(device, convertDiscToNJS(disc));
    }));

    app.get('/addGroup', handle(async (parameters) => {
        const groupBegin = intParameter(parameters, 'groupBegin');
        const groupLength = intParameter(parameters, 'groupLength');
        const title = stringParameter(parameters, 'title');
        const fullWidthTitle = parameters.fullWidthTitle ?? '';
        const disc = await getCachedContent();

        const ungrouped = disc.groups.find(n => n.title === null);
        if (!ungrouped) {
            throw new Error("No groupable tracks on the disc."); // You can only group tracks that aren't already in a different group
        }

        const ungroupedLengthBeforeGroup = ungrouped.tracks.length;

        const thisGroupTracks = ungrouped.tracks.filter(n => n.index >= groupBegin && n.index < groupBegin + groupLength);
        ungrouped.tracks = ungrouped.tracks.filter(n => !thisGroupTracks.includes(n));

        if (ungroupedLengthBeforeGroup - ungrouped.tracks.length !== groupLength) {
            throw new Error('A track cannot be in 2 groups!');
        }

        if (!isSequential(thisGroupTracks.map(n => n.index))) {
            throw new Error('Invalid sequence of tracks!');
        }

        disc.groups.push({
            title,
            fullWidthTitle,
            index: disc.groups.length,
            tracks: thisGroupTracks,
        });
        disc.groups = disc.groups.filter(g => g.tracks.length !== 0).sort((a, b) => a.tracks[0].index - b.tracks[0].index);
        flushCache();
        await rewriteDiscGroups(device, convertDiscToNJS(disc));
    }));

    app.get('/deleteGroup', handle(async (parameters) => {
        const index = intParameter(parameters, 'index');
        const disc = await getCachedContent();

        // The group's tracks become ungrouped
        let ungroupedGroup = disc.groups.find(g => g.title === null);
        if (!ungroupedGroup) {
            ungroupedGroup = {
                index: -1,
                title: null,
                fullWidthTitle: null,
                tracks: [],
            };
            disc.groups.unshift(ungroupedGroup);
        }
        const groupIndex = disc.groups.findIndex(g => g.index === index);
        if (groupIndex >= 0) {
            const deleted = disc.groups.splice(groupIndex, 1)[0];
            ungroupedGroup.tracks = ungroupedGroup.tracks.concat(deleted.tracks);
            ungroupedGroup.tracks.sort((a, b) => a.index - b.index);
        }
        flushCache();
        await rewriteDiscGroups(device, convertDiscToNJS(disc));
    }));

    app.post('/rewriteGroups', handle(async (_, body) => {
        if (!Array.isArray(body.groups)) throw new Error("Missing parameter: groups");
        const disc = await getCachedContent();
        disc.groups = body.groups;
        flushCache();
        await rewriteDiscGroups(device, convertDiscToNJS(disc));
    }));

    app.post('/deleteTracks', handle(async (_, body) => {
        if (!Array.isArray(body.indexes)) throw new Error("Missing parameter: indexes");
        const indexes = body.indexes.map((_, i) => intParameter(body.indexes, i));
        indexes.sort((a, b) => b - a);
        let content = await getCachedContent();
        flushCache();
        for (const index of indexes) {
            // Attempt to get panasonics working correctly (MyNameIsX)
            await device.getTrackTitle(index, false);
            await device.getTrackCount();
            content = recomputeGroupsAfterTrackMove(content, index, -1);
            await device.eraseTrack(index);
            await sleep(100);
        }
        await rewriteDiscGroups(device, convertDiscToNJS(content));
    }));

    app.get('/moveTrack', handle(async (parameters) => {
        const src = intParameter(parameters, 'src');
        const dst = intParameter(parameters, 'dst');
        const updateGroups = parameters.updateGroups !== 'false';

        const content = await getCachedContent();
        flushCache();
        await device.moveTrack(src, dst);
        if (updateGroups) {
            await rewriteDiscGroups(device, convertDiscToNJS(recomputeGroupsAfterTrackMove(content, src, dst)));
        }
    }));

    app.get('/wipeDisc', handle(async () => {
        try {
            await device.stop();
        } catch (ex) {}
        flushCache();
        await device.eraseDisc();
    }));

    app.get('/wipeDiscTitleInfo', handle(async () => {
        flushCache();
        await device.setDiscTitle('');
        await device.setDiscTitle('', true);
    }));

    app.get('/formatToHiMD', handle(async () => {
        flushCache();
        await formatToHiMD(device);
    }));

    // The 'discEject' capability:

    app.get('/eject', handle(async () => {
        flushCache();
        await device.ejectDisc();
    }));

    // The 'playbackControl' capability:

    app.get('/play', handle(() => device.play()));
    app.get('/pause', handle(() => device.pause()));
    app.get('/stop', handle(() => device.stop()));
    app.get('/next', handle(() => device.nextTrack()));
    app.get('/prev', handle(() => device.previousTrack()));
    app.get('/goto', handle((parameters) => device.gotoTrack(intParameter(parameters, 'index'))));
    app.get('/gotoTime', handle((parameters) => device.gotoTime(
        intParameter(parameters, 'index'),
        intParameter(parameters, 'hour'),
        intParameter(parameters, 'minute'),
        intParameter(parameters, 'second'),
        intParameter(parameters, 'frame'),
    )));
    app.get('/getPosition', handle(() => device.getPosition()));

    // The 'trackUpload' capability:

    let session = null;
    app.get('/prepareUpload', handle(async () => {
        await prepareDownload(device);
        session = new MDSession(device);
        await session.init();
    }));
    app.get('/finalizeUpload', handle(async () => {
        if (session) {
            await session.close();
            await device.release();
        }
        session = null;
        flushCache();
    }));

    app.ws('/upload', (ws, req) => {
        if(!session){
            console.log("You need to call /prepareUpload first");
            ws.send(JSON.stringify({ error: "The upload session hasn't been prepared." }));
            ws.close();
            return;
        }
        let {
            title,
            fullWidthTitle,
            format: codec,
            totalLength,
        } = req.query;
        if (!fullWidthTitle) fullWidthTitle = '';
        const WireformatDict = {
            SP: Wireformat.pcm,
            SPM: Wireformat.pcm,
            LP2: Wireformat.lp2,
            LP105: Wireformat.l105kbps,
            LP4: Wireformat.lp4,
        };
        const format = WireformatDict[codec];
        if (title === undefined || title === null || format === undefined) {
            ws.send(JSON.stringify({ error: "Invalid upload parameters." }));
            ws.close();
            return;
        }

        // Encrypted packets are collected first, so the device isn't kept waiting on the network mid-transfer.
        const queue = [];
        let resolveAllReceived;
        const allReceived = new Promise(res => resolveAllReceived = res);
        ws.on('message', _piece => {
            // Deserialize data
            const piece = new Uint8Array(_piece);
            const type = piece[0];
            if(type === 0){
                const iv = piece.subarray(1, 9);
                const key = piece.subarray(9, 17);
                const data = piece.subarray(17);
                queue.push({ iv, key, data });
            }else{
                resolveAllReceived();
            }
        });

        withLockedWebSocket(ws, async () => {
            ws.send(JSON.stringify({ init: true }));
            await allReceived;
            console.log(`Received ${queue.length} packets. Expecting ${totalLength} bytes got ${queue.reduce((a, b) => a + b.data.length, 0)}`);

            let lastTime = 0;
            const mdTrack = new MDTrack(sanitizeHalfWidthTitle(title), format, {
                byteLength: parseInt(totalLength),
            }, 0x400, sanitizeFullWidthTitle(fullWidthTitle), () => ({
                async *[Symbol.asyncIterator](){
                    for(let e of queue){
                        yield e;
                    }
                }
            }));
            await session.downloadTrack(mdTrack, ({
                writtenBytes
            }) => {
                const newTime = new Date().getTime();
                if(newTime - lastTime > 100){
                    ws.send(JSON.stringify({ written: writtenBytes }));
                    lastTime = newTime;
                }
            }, codec === 'SPM' ? DiscFormat.spMono : undefined);

            flushCache();
            ws.send(JSON.stringify({ terminate: true }));
            console.log("Upload completed.");
        });
    });

    // The 'trackDownload' capability (MZ-RH1 only):

    app.ws('/download', (ws, req) => {
        withLockedWebSocket(ws, async () => {
            const index = intParameter(req.query, 'index');
            let lastTime = 0;
            const [format, data] = await readTrackFromDevice(device, index, ({ readBytes, totalBytes }) => {
                const newTime = new Date().getTime();
                if(newTime - lastTime > 100){
                    ws.send(JSON.stringify({ read: readBytes, total: totalBytes }));
                    lastTime = newTime;
                }
            });
            const extension = format === DiscFormat.spMono || format === DiscFormat.spStereo ? 'aea' : 'wav';
            // The file follows as a single binary message
            ws.send(JSON.stringify({ extension, length: data.byteLength }));
            ws.send(data);
            console.log("Download completed.");
        });
    });

    // The 'factoryMode' capability (Sony portables, API revision 3):
    // Mirrors NetMDFactoryUSBService in Web Minidisc Pro. The exploits run here, next to the device.

    app.get('/factory/init', handle(async () => {
        const { factory, esm } = await getFactory();
        return {
            firmware: await getDescriptiveDeviceCode(factory),
            capabilities: getExploitCapabilities(esm),
        };
    }));

    app.get('/factory/readUTOCSector', handle(async (parameters) => {
        const { factory } = await getFactory();
        return Array.from(await readUTOCSector(factory, intParameter(parameters, 'index')));
    }));

    app.post('/factory/writeUTOCSector', handle(async (_, body) => {
        const { factory } = await getFactory();
        if (!Array.isArray(body.data)) throw new Error("Missing parameter: data");
        await writeUTOCSector(factory, intParameter(body, 'index'), new Uint8Array(body.data));
    }));

    app.get('/factory/flushUTOC', handle(async () => {
        const { esm } = await getFactory();
        flushCache();
        await (await esm.require(ForceTOCEdit)).forceTOCEdit();
    }));

    app.get('/factory/runTetris', handle(async () => {
        const { esm } = await getFactory();
        await (await esm.require(Tetris)).playTetris();
    }));

    app.get('/factory/setSPSpeedupActive', handle(async (parameters) => {
        const state = await getFactory();
        const enable = parameters.enable === 'true';
        if (state.fasterTransferEnabled === enable) return;
        state.fasterTransferEnabled = enable;
        if (enable) {
            await state.esm.require(PCMFasterUpload);
        } else {
            await state.esm.unload(PCMFasterUpload);
        }
    }));

    app.get('/factory/enableHiMDFullMode', handle(async () => {
        const { esm } = await getFactory();
        await esm.require(HiMDUSBClassOverride);
    }));

    app.get('/factory/enableMonoUpload', handle(async (parameters) => {
        const { esm } = await getFactory();
        if (parameters.enable === 'true') {
            await esm.require(MonoSPUpload);
        } else {
            await esm.unload(MonoSPUpload);
        }
    }));

    app.get('/factory/setDiscSwapDetection', handle(async (parameters) => {
        const { esm } = await getFactory();
        if (parameters.enable === 'true') {
            await esm.require(DisableDiscDetection);
        } else {
            await esm.unload(DisableDiscDetection);
        }
    }));

    app.get('/factory/enterServiceMode', handle(async () => {
        const { esm } = await getFactory();
        await esm.require(EnterServiceMode);
    }));

    // Returns whether the slower exploit was asked for, but isn't compatible with the device
    app.get('/factory/prepareDownload', handle(async (parameters) => {
        const state = await getFactory();
        let useSlowerExploit = parameters.useSlowerExploit === 'true';
        const fellBack = useSlowerExploit && !isCompatible(CachedSectorControlDownload, state.esm.device);
        if (fellBack) useSlowerExploit = false;
        const exploitConstructor = useSlowerExploit
            ? CachedSectorControlDownload
            : getBestSuited(AtracRecovery, state.esm.device);
        state.atracDownloader = await state.esm.require(exploitConstructor);
        return fellBack;
    }));

    app.get('/factory/finalizeDownload', handle(async () => {
        const state = await getFactory();
        if (state.atracDownloader) await state.esm.unload(state.atracDownloader);
        state.atracDownloader = null;
    }));

    app.ws('/factory/readRAM', (ws) => factoryWebSocket(ws, async ({ progress }) => {
        const { factory } = await getFactory();
        const firmwareVersion = await getDescriptiveDeviceCode(factory);
        const ramSize = firmwareVersion.startsWith('R') ? 0x4800 : 0x9000;
        const readSlices = [];
        for (let i = 0; i < ramSize; i += 0x10) {
            readSlices.push(await cleanRead(factory, i + 0x02000000, 0x10, MemoryType.MAPPED));
            progress({ readBytes: i, totalBytes: ramSize });
        }
        return { buffers: [Buffer.concat(readSlices)] };
    }));

    app.ws('/factory/readFirmware', (ws) => factoryWebSocket(ws, async ({ progress }) => {
        const { esm } = await getFactory();
        const firmwareRipper = await esm.require(FirmwareDumper);
        const { rom, ram, dram } = await firmwareRipper.readFirmware(progress);
        const parts = dram ? { rom, ram, dram } : { rom, ram };
        return { value: Object.keys(parts), buffers: Object.values(parts) };
    }));

    app.ws('/factory/downloadTrack', (ws, req) => factoryWebSocket(ws, async ({ progress, ask, isCancelled }) => {
        const { atracDownloader } = await getFactory();
        if (!atracDownloader) throw new Error("You need to call /factory/prepareDownload first");
        const track = intParameter(req.query, 'track');
        const config = {
            ...JSON.parse(req.query.config ?? '{}'),
            shouldCancelImmediately: isCancelled,
            handleBadSector: async (address, count, seconds) => {
                console.log(`Bad sector at ${address} (DRAM sector ${count}, ${seconds.toFixed(2)}s), asking the client...`);
                const answer = await ask({ badSector: { address, count, seconds } });
                console.log(`Bad sector at ${address}: the client chose '${answer}'.`);
                return answer;
            },
        };
        if (req.query.neraw === 'true') {
            const data = await atracDownloader.downloadTrackWithMarkers(track, progress, {
                ...config,
                includeMetadataSection: true,
                removeLPBytes: 'never',
            });
            return { value: { extension: 'neraw' }, buffers: [data] };
        }
        const { data, extension } = await atracDownloader.downloadTrack(track, progress, config);
        return { value: { extension }, buffers: [data] };
    }));

    // SP (ATRAC1) uploads. The client sends the raw ATRAC data; it's reshaped by the exploit, then encrypted here.
    app.ws('/factory/uploadSP', (ws, req) => factoryWebSocket(ws, async ({ progress, receiveData }) => {
        const state = await getFactory();
        const { esm } = state;
        const { title = '', fullWidthTitle = '' } = req.query;
        const mono = req.query.mono === 'true';
        const data = Buffer.concat(await receiveData());
        if (!session) throw new Error("The upload session hasn't been prepared.");

        // The patch memory is too small to accomodate for both ATRAC1Upload and PCMFasterUpload.
        if (state.fasterTransferEnabled) {
            await esm.unload(PCMFasterUpload);
        }

        let total = data.byteLength;
        let written = 0;
        let encrypted = 0;
        const worker = new Worker(encryptWorkerPath);
        const packetIterator = makeGetAsyncPacketIteratorOnWorkerThread(worker, ({ encryptedBytes }) => {
            encrypted = encryptedBytes;
            progress({ written, encrypted, total });
        });

        let mdTrack = new MDTrack(sanitizeHalfWidthTitle(title), Wireformat.l105kbps,
            data.buffer.slice(data.byteOffset, data.byteOffset + data.byteLength), 0x400,
            sanitizeFullWidthTitle(fullWidthTitle), packetIterator);
        let index = -1;
        try {
            await esm.envelop(SPUpload, mono ? 1 : 2, async spUpload => {
                mdTrack = spUpload.prepareTrack(mdTrack);
                total = mdTrack.data.byteLength;
                [index] = await session.downloadTrack(mdTrack, ({ writtenBytes }) => {
                    written = writtenBytes;
                    progress({ written, encrypted, total });
                });
            });
        } finally {
            worker.terminate();
            flushCache();
        }

        if (state.fasterTransferEnabled) {
            await esm.require(PCMFasterUpload);
        }
        console.log("SP upload completed.");
        return { value: index };
    }));

    app.get('/upload', handle(() => { throw new Error("This is a WebSocket-only endpoint."); }));
    app.get('/download', handle(() => { throw new Error("This is a WebSocket-only endpoint."); }));
}
