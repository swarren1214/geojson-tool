import { useEffect, useMemo, useRef, useState, type MouseEvent as ReactMouseEvent, type ReactNode } from 'react';
import maplibregl, { GeoJSONSource, LngLatBoundsLike, Map } from 'maplibre-gl';
import { AnimatePresence, motion } from 'framer-motion';
import type { Feature, GeoJsonProperties, Geometry, MultiPolygon, Point, Polygon } from 'geojson';
import {
  Braces,
  Check,
  ChevronDown,
  ChevronUp,
  Download,
  FileUp,
  FolderTree,
  Loader2,
  MapPinned,
  Merge,
  Pencil,
  PenLine,
  Redo2,
  Scissors,
  Tag,
  Trash2,
  Undo2,
  X,
} from 'lucide-react';
import type { AnyFeatureCollection } from './types';
import {
  getCollectionBounds,
  mergePolygons,
  parseGeoJson,
  separatePolygonParts,
  smoothPolygonFeature,
  smoothPolygonsInCollection,
  type SmoothAlgorithm,
  splitPolygonsByStates,
} from './lib/geojson';
import { getEmptyStateBoundaries, getStateBoundaries } from './lib/stateBoundaries';

const EMPTY_COLLECTION: AnyFeatureCollection = {
  type: 'FeatureCollection',
  features: [],
};

const BASEMAP_STYLE = 'https://basemaps.cartocdn.com/gl/voyager-gl-style/style.json';
const POLYGON_FILL_COLOR = '#2a9d8f';
const POLYGON_SELECTED_FILL_COLOR = '#f59e0b';
const POLYGON_HOVER_FILL_COLOR = '#0f172a';

function getPolygonColorForId(appFeatureId: string): string {
  // Hash the feature id into a stable hue so each polygon keeps its own color.
  let hash = 0;
  for (let i = 0; i < appFeatureId.length; i++) {
    hash = (hash << 5) - hash + appFeatureId.charCodeAt(i);
    hash |= 0;
  }

  const hue = Math.abs(hash) % 360;
  return `hsl(${hue} 62% 58%)`;
}

function buildPolygonColorById(data: AnyFeatureCollection): Record<string, string> {
  const colorById: Record<string, string> = {};
  const usedHueBuckets = new Set<number>();

  data.features.forEach((feature, index) => {
    if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const appFeatureId = feature.properties?.appFeatureId;
    if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
      return;
    }

    let hue = Math.abs(
      appFeatureId.split('').reduce((acc, char) => ((acc << 5) - acc + char.charCodeAt(0)) | 0, index),
    ) % 360;
    let bucket = Math.floor(hue / 8);

    // Spread neighboring IDs apart so split siblings do not collapse into the same visible color.
    while (usedHueBuckets.has(bucket)) {
      hue = (hue + 137) % 360;
      bucket = Math.floor(hue / 8);
    }

    usedHueBuckets.add(bucket);
    colorById[appFeatureId] = `hsl(${hue} 62% 58%)`;
  });

  return colorById;
}

function withPolygonColors(
  data: AnyFeatureCollection,
  colorById: Record<string, string>,
): AnyFeatureCollection {
  return {
    ...data,
    features: data.features.map((feature) => {
      if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
        return feature;
      }

      const appFeatureId = feature.properties?.appFeatureId;
      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return feature;
      }

      return {
        ...feature,
        properties: {
          ...feature.properties,
          polygonColor: colorById[appFeatureId] || getPolygonColorForId(appFeatureId),
        },
      };
    }),
  };
}

function waitForUiPaint(): Promise<void> {
  return new Promise((resolve) => {
    window.requestAnimationFrame(() => resolve());
  });
}

function parseCsvRows(rawText: string): string[][] {
  const rows: string[][] = [];
  let row: string[] = [];
  let cell = '';
  let inQuotes = false;

  for (let i = 0; i < rawText.length; i++) {
    const char = rawText[i];

    if (char === '"') {
      const isEscapedQuote = inQuotes && rawText[i + 1] === '"';
      if (isEscapedQuote) {
        cell += '"';
        i += 1;
      } else {
        inQuotes = !inQuotes;
      }
      continue;
    }

    if (char === ',' && !inQuotes) {
      row.push(cell.trim());
      cell = '';
      continue;
    }

    if ((char === '\n' || char === '\r') && !inQuotes) {
      if (char === '\r' && rawText[i + 1] === '\n') {
        i += 1;
      }

      row.push(cell.trim());
      cell = '';

      if (row.some((value) => value !== '')) {
        rows.push(row);
      }

      row = [];
      continue;
    }

    cell += char;
  }

  row.push(cell.trim());
  if (row.some((value) => value !== '')) {
    rows.push(row);
  }

  return rows;
}

function parseCsvPointCollection(rawText: string, fileName: string, fileId: string): {
  data: AnyFeatureCollection;
  importedCount: number;
  skippedCount: number;
} {
  const rows = parseCsvRows(rawText);
  if (!rows.length) {
    throw new Error('CSV is empty.');
  }

  const normalizedHeader = rows[0].map((value) => value.trim().toLowerCase());
  const latHeaderNames = new Set(['lat', 'latitude', 'y']);
  const lonHeaderNames = new Set(['lon', 'lng', 'long', 'longitude', 'x']);

  const latHeaderIndex = normalizedHeader.findIndex((value) => latHeaderNames.has(value));
  const lonHeaderIndex = normalizedHeader.findIndex((value) => lonHeaderNames.has(value));
  const hasHeader = latHeaderIndex >= 0 && lonHeaderIndex >= 0;

  const latIndex = hasHeader ? latHeaderIndex : 0;
  const lonIndex = hasHeader ? lonHeaderIndex : 1;

  if (!hasHeader && rows[0].length < 2) {
    throw new Error('CSV must include lat/lon columns or at least two coordinate columns.');
  }

  const features: Feature<Point, GeoJsonProperties>[] = [];
  let skippedCount = 0;
  const startRow = hasHeader ? 1 : 0;

  for (let i = startRow; i < rows.length; i++) {
    const row = rows[i];
    const latValue = row[latIndex];
    const lonValue = row[lonIndex];

    const lat = typeof latValue === 'string' ? Number.parseFloat(latValue) : Number.NaN;
    const lon = typeof lonValue === 'string' ? Number.parseFloat(lonValue) : Number.NaN;

    if (!Number.isFinite(lat) || !Number.isFinite(lon) || lat < -90 || lat > 90 || lon < -180 || lon > 180) {
      skippedCount += 1;
      continue;
    }

    features.push({
      type: 'Feature',
      geometry: {
        type: 'Point',
        coordinates: [lon, lat],
      },
      properties: {
        csvSourceFileId: fileId,
        csvSourceFile: fileName,
        csvRowNumber: i + 1,
      },
    });
  }

  if (!features.length) {
    throw new Error('No valid coordinates found in CSV.');
  }

  return {
    data: {
      type: 'FeatureCollection',
      features,
    },
    importedCount: features.length,
    skippedCount,
  };
}

type UploadedFileMeta = {
  id: string;
  name: string;
  featureCount: number;
  polygonCount: number;
};

type CsvPointFileMeta = {
  id: string;
  name: string;
  pointCount: number;
};

type ContextMenuState = {
  open: boolean;
  x: number;
  y: number;
  appFeatureId: string | null;
  nameDraft: string;
};

type PolygonListItem = {
  appFeatureId: string;
  sourceFileId: string;
  sourceFileName: string;
  defaultName: string;
  isMultiPolygon: boolean;
  stateName?: string;
  stateBadge?: string;
  splitByState: boolean;
};

type SmoothPanelState = {
  open: boolean;
  appFeatureId: string | null;
  algorithm: SmoothAlgorithm;
  sensitivity: number;
  x: number;
  y: number;
};

type WorkspaceSnapshot = {
  displayData: AnyFeatureCollection;
  csvPointData: AnyFeatureCollection;
  csvPointFiles: CsvPointFileMeta[];
  uploadedFiles: UploadedFileMeta[];
  polygonNames: Record<string, string>;
};

type GeometryMetrics = {
  vertices: number;
  edges: number;
};

type ToolbarActionButtonProps = {
  onClick: () => void;
  disabled: boolean;
  ariaLabel: string;
  tooltip: string;
  className: string;
  children: ReactNode;
};

type PolygonIconActionButtonProps = {
  onClick: (event: ReactMouseEvent<HTMLButtonElement>) => void;
  ariaLabel: string;
  tooltip: string;
  className: string;
  disabled?: boolean;
  children: ReactNode;
};

type OperationAlertState = {
  type: 'success' | 'error';
  message: string;
};

const MAX_HISTORY_ENTRIES = 100;

function sanitizeFileName(value: string): string {
  const trimmed = value.trim();
  if (!trimmed) {
    return 'polygon';
  }

  return trimmed
    .replace(/[^a-zA-Z0-9-_ ]+/g, '')
    .replace(/\s+/g, '-')
    .replace(/-+/g, '-')
    .toLowerCase();
}

const STATE_NAME_TO_CODE: Record<string, string> = {
  Alabama: 'AL',
  Alaska: 'AK',
  Arizona: 'AZ',
  Arkansas: 'AR',
  California: 'CA',
  Colorado: 'CO',
  Connecticut: 'CT',
  Delaware: 'DE',
  'District of Columbia': 'DC',
  Florida: 'FL',
  Georgia: 'GA',
  Hawaii: 'HI',
  Idaho: 'ID',
  Illinois: 'IL',
  Indiana: 'IN',
  Iowa: 'IA',
  Kansas: 'KS',
  Kentucky: 'KY',
  Louisiana: 'LA',
  Maine: 'ME',
  Maryland: 'MD',
  Massachusetts: 'MA',
  Michigan: 'MI',
  Minnesota: 'MN',
  Mississippi: 'MS',
  Missouri: 'MO',
  Montana: 'MT',
  Nebraska: 'NE',
  Nevada: 'NV',
  'New Hampshire': 'NH',
  'New Jersey': 'NJ',
  'New Mexico': 'NM',
  'New York': 'NY',
  'North Carolina': 'NC',
  'North Dakota': 'ND',
  Ohio: 'OH',
  Oklahoma: 'OK',
  Oregon: 'OR',
  Pennsylvania: 'PA',
  'Rhode Island': 'RI',
  'South Carolina': 'SC',
  'South Dakota': 'SD',
  Tennessee: 'TN',
  Texas: 'TX',
  Utah: 'UT',
  Vermont: 'VT',
  Virginia: 'VA',
  Washington: 'WA',
  'West Virginia': 'WV',
  Wisconsin: 'WI',
  Wyoming: 'WY',
};

function getStateCodeLabel(stateName: string | undefined): string | undefined {
  if (typeof stateName !== 'string') {
    return undefined;
  }

  const normalizedName = stateName.trim();
  if (!normalizedName) {
    return undefined;
  }

  return STATE_NAME_TO_CODE[normalizedName] || normalizedName;
}

function getPolygonDefaultName(feature: Feature<Geometry, GeoJsonProperties>, index: number): string {
  const fromProp = feature.properties?.polygonName;
  if (typeof fromProp === 'string' && fromProp.trim()) {
    return fromProp.trim();
  }

  const stateName = feature.properties?.stateName;
  if (typeof stateName === 'string' && stateName.trim()) {
    return `State Piece: ${stateName.trim()}`;
  }

  return `Polygon ${index + 1}`;
}

function annotateImportedCollection(data: AnyFeatureCollection, fileId: string, fileName: string): AnyFeatureCollection {
  return {
    ...data,
    features: data.features.map((feature, index) => ({
      ...feature,
      properties: {
        ...feature.properties,
        sourceFileId: fileId,
        sourceFileName: fileName,
        sourceFeatureIndex: index,
        appFeatureId: `feature-${fileId}-${Date.now()}-${index}`,
      },
    })),
  };
}

function withFeatureIds(data: AnyFeatureCollection, prefix: string): AnyFeatureCollection {
  const seen = new Set<string>();
  const runStamp = Date.now();

  return {
    ...data,
    features: data.features.map((feature, index) => {
      const existingId = feature.properties?.appFeatureId;
      const normalizedExistingId =
        typeof existingId === 'string' && existingId.trim() ? existingId.trim() : null;

      const appFeatureId =
        normalizedExistingId && !seen.has(normalizedExistingId)
          ? normalizedExistingId
          : `${prefix}-${runStamp}-${index}-${Math.random().toString(36).slice(2, 8)}`;

      seen.add(appFeatureId);

      return {
        ...feature,
        properties: {
          ...feature.properties,
          appFeatureId,
        },
      };
    }),
  };
}

function isPolygonFeature(feature: Feature<Geometry, GeoJsonProperties>): boolean {
  return feature.geometry?.type === 'Polygon' || feature.geometry?.type === 'MultiPolygon';
}

function countFeatureGeometryMetrics(
  feature: Feature<Geometry, GeoJsonProperties> | undefined,
): GeometryMetrics {
  if (!feature || !isPolygonFeature(feature)) {
    return { vertices: 0, edges: 0 };
  }

  let vertices = 0;
  let edges = 0;

  const countRing = (ring: number[][]) => {
    if (!Array.isArray(ring) || ring.length < 2) {
      return;
    }

    const first = ring[0];
    const last = ring[ring.length - 1];
    const isClosed = first[0] === last[0] && first[1] === last[1];
    const ringVertices = isClosed ? Math.max(0, ring.length - 1) : ring.length;

    vertices += ringVertices;
    edges += ringVertices > 1 ? (isClosed ? ringVertices : ringVertices - 1) : 0;
  };

  if (feature.geometry.type === 'Polygon') {
    const polygonFeature = feature as Feature<Polygon, GeoJsonProperties>;
    polygonFeature.geometry.coordinates.forEach((ring) => countRing(ring));
    return { vertices, edges };
  }

  const multiPolygonFeature = feature as Feature<MultiPolygon, GeoJsonProperties>;
  multiPolygonFeature.geometry.coordinates.forEach((polygon) => {
    polygon.forEach((ring) => countRing(ring));
  });

  return { vertices, edges };
}

function ToolbarActionButton({
  onClick,
  disabled,
  ariaLabel,
  tooltip,
  className,
  children,
}: ToolbarActionButtonProps) {
  return (
    <div className="group relative flex-1 min-w-0">
      <button onClick={onClick} disabled={disabled} aria-label={ariaLabel} title={tooltip} className={className}>
        {children}
      </button>
      <span
        role="tooltip"
        className="pointer-events-none absolute -top-2 left-1/2 z-20 -translate-x-1/2 -translate-y-full whitespace-nowrap rounded-md bg-slate-900 px-2 py-1 text-[11px] font-semibold text-white opacity-0 shadow-sm transition group-hover:opacity-100 group-focus-within:opacity-100"
      >
        {tooltip}
      </span>
    </div>
  );
}

function PolygonIconActionButton({
  onClick,
  ariaLabel,
  tooltip,
  className,
  disabled = false,
  children,
}: PolygonIconActionButtonProps) {
  return (
    <div className="group relative">
      <button
        onClick={onClick}
        title={tooltip}
        aria-label={ariaLabel}
        disabled={disabled}
        className={`${className} ${disabled ? 'cursor-not-allowed opacity-50' : ''}`}
      >
        {children}
      </button>
      <span
        role="tooltip"
        className="pointer-events-none absolute -top-1 left-1/2 z-20 -translate-x-1/2 -translate-y-full whitespace-nowrap rounded-md bg-slate-900 px-2 py-1 text-[10px] font-semibold text-white opacity-0 shadow-sm transition group-hover:opacity-100 group-focus-within:opacity-100"
      >
        {tooltip}
      </span>
    </div>
  );
}

export default function App() {
  const mapContainerRef = useRef<HTMLDivElement | null>(null);
  const fileInputRef = useRef<HTMLInputElement | null>(null);
  const csvPointFileInputRef = useRef<HTMLInputElement | null>(null);
  const mapRef = useRef<Map | null>(null);

  const [displayData, setDisplayData] = useState<AnyFeatureCollection>(EMPTY_COLLECTION);
  const [csvPointData, setCsvPointData] = useState<AnyFeatureCollection>(EMPTY_COLLECTION);
  const [csvPointFiles, setCsvPointFiles] = useState<CsvPointFileMeta[]>([]);
  const [uploadedFiles, setUploadedFiles] = useState<UploadedFileMeta[]>([]);
  const [error, setError] = useState<string>('');
  const [isDragOverUpload, setIsDragOverUpload] = useState<boolean>(false);
  const [isDragOverCsvUpload, setIsDragOverCsvUpload] = useState<boolean>(false);
  const [showStates, setShowStates] = useState<boolean>(false);
  const [isSplittingAll, setIsSplittingAll] = useState<boolean>(false);
  const [splittingFeatureIds, setSplittingFeatureIds] = useState<Set<string>>(new Set());
  const [operationAlert, setOperationAlert] = useState<OperationAlertState | null>(null);
  const [collapsedPolygonIds, setCollapsedPolygonIds] = useState<Set<string>>(new Set());
  const [polygonNames, setPolygonNames] = useState<Record<string, string>>({});
  const [editingPolygonId, setEditingPolygonId] = useState<string | null>(null);
  const [editingPolygonNameDraft, setEditingPolygonNameDraft] = useState<string>('');
  const [mergeMode, setMergeMode] = useState<boolean>(false);
  const [selectedForMerge, setSelectedForMerge] = useState<Set<string>>(new Set());
  const [selectedFeatureId, setSelectedFeatureId] = useState<string | null>(null);
  const [undoStack, setUndoStack] = useState<WorkspaceSnapshot[]>([]);
  const [redoStack, setRedoStack] = useState<WorkspaceSnapshot[]>([]);
  const [smoothPanel, setSmoothPanel] = useState<SmoothPanelState>({
    open: false,
    appFeatureId: null,
    algorithm: 'chaikin',
    sensitivity: 40,
    x: 0,
    y: 0,
  });
  const [contextMenu, setContextMenu] = useState<ContextMenuState>({
    open: false,
    x: 0,
    y: 0,
    appFeatureId: null,
    nameDraft: '',
  });

  const displayDataRef = useRef<AnyFeatureCollection>(displayData);
  const csvPointDataRef = useRef<AnyFeatureCollection>(csvPointData);
  const showStatesRef = useRef<boolean>(showStates);
  const polygonNameByIdRef = useRef<Record<string, string>>({});
  const hoveredFeatureIdRef = useRef<string | null>(null);
  const selectedFeatureIdRef = useRef<string | null>(null);
  const pendingFitBoundsRef = useRef<LngLatBoundsLike | null>(null);
  const uploadDragDepthRef = useRef<number>(0);
  const csvUploadDragDepthRef = useRef<number>(0);
  const polygonColorByIdRef = useRef<Record<string, string>>({});

  function createWorkspaceSnapshot(): WorkspaceSnapshot {
    return {
      displayData,
      csvPointData,
      csvPointFiles,
      uploadedFiles,
      polygonNames,
    };
  }

  function applyWorkspaceSnapshot(snapshot: WorkspaceSnapshot) {
    setDisplayData(snapshot.displayData);
    setCsvPointData(snapshot.csvPointData);
    setCsvPointFiles(snapshot.csvPointFiles);
    setUploadedFiles(snapshot.uploadedFiles);
    setPolygonNames(snapshot.polygonNames);
    setMergeMode(false);
    setSelectedForMerge(new Set());
    closeContextMenu();
    closePolygonMenu();
    closeSmoothPanel();
    setError('');

    const map = mapRef.current;
    if (map) {
      clearHoveredFeature(map);
      clearSelectedFeature(map);
    }
  }

  function recordHistorySnapshot(snapshot = createWorkspaceSnapshot()) {
    setUndoStack((previous) => [...previous.slice(-(MAX_HISTORY_ENTRIES - 1)), snapshot]);
    setRedoStack([]);
  }

  function handleUndo() {
    if (!undoStack.length) {
      return;
    }

    const previous = undoStack[undoStack.length - 1];
    setUndoStack((stack) => stack.slice(0, -1));
    setRedoStack((stack) => [...stack, createWorkspaceSnapshot()]);
    applyWorkspaceSnapshot(previous);
  }

  function handleRedo() {
    if (!redoStack.length) {
      return;
    }

    const next = redoStack[redoStack.length - 1];
    setRedoStack((stack) => stack.slice(0, -1));
    setUndoStack((stack) => [...stack.slice(-(MAX_HISTORY_ENTRIES - 1)), createWorkspaceSnapshot()]);
    applyWorkspaceSnapshot(next);
  }

  function shouldIgnoreHistoryShortcut(target: EventTarget | null): boolean {
    if (!(target instanceof HTMLElement)) {
      return false;
    }

    const tagName = target.tagName.toLowerCase();
    return target.isContentEditable || tagName === 'input' || tagName === 'textarea' || tagName === 'select';
  }

  function closeContextMenu() {
    setContextMenu({
      open: false,
      x: 0,
      y: 0,
      appFeatureId: null,
      nameDraft: '',
    });
  }

  function closePolygonMenu() {
    // Polygon actions are rendered inline on each card, so no menu state is needed.
  }

  function closeSmoothPanel() {
    setSmoothPanel((previous) => ({
      ...previous,
      open: false,
      appFeatureId: null,
    }));
  }

  function fitMapToBounds(bounds: LngLatBoundsLike) {
    const map = mapRef.current;
    if (!map) {
      return;
    }

    if (!map.isStyleLoaded()) {
      pendingFitBoundsRef.current = bounds;
      return;
    }

    pendingFitBoundsRef.current = null;
    map.fitBounds(bounds, {
      padding: 48,
      duration: 700,
    });
  }

  function fitMapToCollection(data: AnyFeatureCollection) {
    const bounds = getCollectionBounds(data);
    if (bounds) {
      fitMapToBounds(bounds as LngLatBoundsLike);
    }
  }

  useEffect(() => {
    displayDataRef.current = displayData;
  }, [displayData]);

  useEffect(() => {
    csvPointDataRef.current = csvPointData;
  }, [csvPointData]);

  const polygonColorById = useMemo(() => buildPolygonColorById(displayData), [displayData]);

  useEffect(() => {
    polygonColorByIdRef.current = polygonColorById;
  }, [polygonColorById]);

  useEffect(() => {
    if (!operationAlert) {
      return;
    }

    const timeoutId = window.setTimeout(() => {
      setOperationAlert(null);
    }, 4500);

    return () => {
      window.clearTimeout(timeoutId);
    };
  }, [operationAlert]);

  useEffect(() => {
    showStatesRef.current = showStates;
  }, [showStates]);

  const polygonItems = useMemo<PolygonListItem[]>(() => {
    return displayData.features.flatMap((feature, index) => {
      if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
        return [];
      }

      const appFeatureId = feature.properties?.appFeatureId;
      const sourceFileId = feature.properties?.sourceFileId;
      const sourceFileName = feature.properties?.sourceFileName;

      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return [];
      }

      const stateName =
        typeof feature.properties?.stateName === 'string' ? feature.properties.stateName : undefined;

      return [
        {
          appFeatureId,
          sourceFileId: typeof sourceFileId === 'string' ? sourceFileId : 'unknown',
          sourceFileName: typeof sourceFileName === 'string' ? sourceFileName : 'Unknown File',
          defaultName: getPolygonDefaultName(feature as Feature<Geometry, GeoJsonProperties>, index),
          isMultiPolygon: feature.geometry?.type === 'MultiPolygon',
          stateName,
          stateBadge: getStateCodeLabel(stateName),
          splitByState: Boolean(feature.properties?.splitByState),
        },
      ];
    });
  }, [displayData]);

  const polygonNameById = useMemo(() => {
    const lookup: Record<string, string> = {};
    polygonItems.forEach((item) => {
      lookup[item.appFeatureId] = polygonNames[item.appFeatureId] || item.defaultName;
    });
    return lookup;
  }, [polygonItems, polygonNames]);

  const polygonMetricsById = useMemo<Record<string, GeometryMetrics>>(() => {
    const lookup: Record<string, GeometryMetrics> = {};
    displayData.features.forEach((feature) => {
      const appFeatureId = feature.properties?.appFeatureId;
      if (typeof appFeatureId !== 'string' || !appFeatureId.trim()) {
        return;
      }

      lookup[appFeatureId] = countFeatureGeometryMetrics(feature as Feature<Geometry, GeoJsonProperties>);
    });
    return lookup;
  }, [displayData]);

  const smoothPreviewData = useMemo<AnyFeatureCollection>(() => {
    if (!smoothPanel.open || !smoothPanel.appFeatureId) {
      return displayData;
    }

    return {
      type: 'FeatureCollection',
      features: displayData.features.map((feature) => {
        if (feature.properties?.appFeatureId !== smoothPanel.appFeatureId) {
          return feature;
        }

        if (!isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>)) {
          return feature;
        }

        return smoothPolygonFeature(feature as Parameters<typeof smoothPolygonFeature>[0], {
          algorithm: smoothPanel.algorithm,
          sensitivity: smoothPanel.sensitivity,
        });
      }),
    };
  }, [displayData, smoothPanel]);

  const smoothGeometryMetrics = useMemo<
    | {
        original: GeometryMetrics;
        preview: GeometryMetrics;
      }
    | null
  >(() => {
    if (!smoothPanel.open || !smoothPanel.appFeatureId) {
      return null;
    }

    const originalFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === smoothPanel.appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;
    const previewFeature = smoothPreviewData.features.find(
      (feature) => feature.properties?.appFeatureId === smoothPanel.appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    return {
      original: countFeatureGeometryMetrics(originalFeature),
      preview: countFeatureGeometryMetrics(previewFeature),
    };
  }, [displayData, smoothPreviewData, smoothPanel.appFeatureId, smoothPanel.open]);

  useEffect(() => {
    polygonNameByIdRef.current = polygonNameById;
  }, [polygonNameById]);

  useEffect(() => {
    if (!selectedFeatureId) {
      return;
    }

    const el = document.querySelector<HTMLElement>(`[data-appfeatureid="${CSS.escape(selectedFeatureId)}"]`);
    el?.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }, [selectedFeatureId]);

  const filesWithPolygons = useMemo(() => {
    const byFileId: Record<string, PolygonListItem[]> = {};

    polygonItems.forEach((item) => {
      if (!byFileId[item.sourceFileId]) {
        byFileId[item.sourceFileId] = [];
      }
      byFileId[item.sourceFileId].push(item);
    });

    const primaryGroups = uploadedFiles.map((file) => ({
      id: file.id,
      name: file.name,
      polygons: byFileId[file.id] || [],
      featureCount: file.featureCount,
      polygonCount: file.polygonCount,
    }));

    const knownIds = new Set(uploadedFiles.map((file) => file.id));
    const fallbackGroups = Object.entries(byFileId)
      .filter(([fileId]) => !knownIds.has(fileId))
      .map(([fileId, polygons]) => ({
        id: fileId,
        name: polygons[0]?.sourceFileName || 'Unknown File',
        polygons,
        featureCount: polygons.length,
        polygonCount: polygons.length,
      }));

    return [...primaryGroups, ...fallbackGroups];
  }, [uploadedFiles, polygonItems]);

  useEffect(() => {
    setPolygonNames((previous) => {
      const next: Record<string, string> = {};

      polygonItems.forEach((item) => {
        next[item.appFeatureId] = previous[item.appFeatureId] || item.defaultName;
      });

      return next;
    });
  }, [polygonItems]);

  useEffect(() => {
    if (!editingPolygonId) {
      return;
    }

    const exists = polygonItems.some((item) => item.appFeatureId === editingPolygonId);
    if (!exists) {
      setEditingPolygonId(null);
      setEditingPolygonNameDraft('');
    }
  }, [editingPolygonId, polygonItems]);

  useEffect(() => {
    setCollapsedPolygonIds((previous) => {
      const validIds = new Set(polygonItems.map((item) => item.appFeatureId));
      const next = new Set<string>();

      previous.forEach((id) => {
        if (validIds.has(id)) {
          next.add(id);
        }
      });

      return next;
    });
  }, [polygonItems]);

  function togglePolygonExpanded(appFeatureId: string) {
    setCollapsedPolygonIds((previous) => {
      const next = new Set(previous);
      if (next.has(appFeatureId)) {
        next.delete(appFeatureId);
      } else {
        next.add(appFeatureId);
      }
      return next;
    });
  }

  function clearHoveredFeature(map: Map) {
    if (!hoveredFeatureIdRef.current) {
      return;
    }

    const source = map.getSource('geojson-data');
    if (source) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: hoveredFeatureIdRef.current,
        },
        { hover: false },
      );
    }

    hoveredFeatureIdRef.current = null;
  }

  function clearSelectedFeature(map: Map) {
    if (!selectedFeatureIdRef.current) {
      return;
    }

    const source = map.getSource('geojson-data');
    if (source) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: false },
      );
    }

    selectedFeatureIdRef.current = null;
    setSelectedFeatureId(null);
  }

  function setSelectedFeature(map: Map, appFeatureId: string | null) {
    if (selectedFeatureIdRef.current && selectedFeatureIdRef.current !== appFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: false },
      );
    }

    selectedFeatureIdRef.current = appFeatureId;
    setSelectedFeatureId(appFeatureId);

    if (appFeatureId && map.getSource('geojson-data')) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: appFeatureId,
        },
        { selected: true },
      );
    }
  }

  function setHoveredFeature(map: Map, nextFeatureId: string | null) {
    if (hoveredFeatureIdRef.current && hoveredFeatureIdRef.current !== nextFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: hoveredFeatureIdRef.current,
        },
        { hover: false },
      );
    }

    if (nextFeatureId && hoveredFeatureIdRef.current !== nextFeatureId) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: nextFeatureId,
        },
        { hover: true },
      );
    }

    hoveredFeatureIdRef.current = nextFeatureId;
  }

  async function refreshStateBoundarySource(map: Map) {
    const stateSource = map.getSource('state-boundaries') as GeoJSONSource | undefined;
    if (!stateSource) {
      return;
    }

    try {
      const states = await getStateBoundaries();
      stateSource.setData(states);
      setError('');
    } catch {
      setError('Could not load detailed state boundaries.');
    }
  }

  function ensureMapDataLayers(map: Map) {
    if (!map.getSource('state-boundaries')) {
      map.addSource('state-boundaries', {
        type: 'geojson',
        data: getEmptyStateBoundaries(),
      });
    }

    if (!map.getLayer('state-boundaries-line')) {
      map.addLayer({
        id: 'state-boundaries-line',
        type: 'line',
        source: 'state-boundaries',
        paint: {
          'line-color': '#0b3d91',
          'line-opacity': 0.55,
          'line-width': 1,
        },
      });
    }

    if (!map.getSource('geojson-data')) {
      map.addSource('geojson-data', {
        type: 'geojson',
        data: EMPTY_COLLECTION,
        promoteId: 'appFeatureId',
      });
    }

    if (!map.getSource('csv-point-data')) {
      map.addSource('csv-point-data', {
        type: 'geojson',
        data: EMPTY_COLLECTION,
        cluster: true,
        clusterMaxZoom: 12,
        clusterRadius: 48,
      });
    }

    if (!map.getLayer('geojson-fill')) {
      map.addLayer({
        id: 'geojson-fill',
        type: 'fill',
        source: 'geojson-data',
        filter: ['in', ['geometry-type'], ['literal', ['Polygon', 'MultiPolygon']]],
        paint: {
          'fill-color': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            POLYGON_SELECTED_FILL_COLOR,
            ['boolean', ['feature-state', 'hover'], false],
            POLYGON_HOVER_FILL_COLOR,
            ['coalesce', ['get', 'polygonColor'], POLYGON_FILL_COLOR],
          ],
          'fill-opacity': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            0.72,
            ['boolean', ['feature-state', 'hover'], false],
            0.62,
            0.35,
          ],
        },
      });
    }

    if (!map.getLayer('geojson-line')) {
      map.addLayer({
        id: 'geojson-line',
        type: 'line',
        source: 'geojson-data',
        paint: {
          'line-color': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            '#7c2d12',
            ['boolean', ['feature-state', 'hover'], false],
            '#020617',
            '#111827',
          ],
          'line-width': [
            'case',
            ['boolean', ['feature-state', 'selected'], false],
            4.2,
            ['boolean', ['feature-state', 'hover'], false],
            3.2,
            2,
          ],
        },
      });
    }

    if (!map.getLayer('geojson-point')) {
      map.addLayer({
        id: 'geojson-point',
        type: 'circle',
        source: 'geojson-data',
        filter: ['==', ['geometry-type'], 'Point'],
        paint: {
          'circle-radius': 5,
          'circle-color': '#111827',
          'circle-stroke-color': '#fff7ed',
          'circle-stroke-width': 2,
        },
      });
    }

    if (!map.getLayer('csv-point-clusters')) {
      map.addLayer({
        id: 'csv-point-clusters',
        type: 'circle',
        source: 'csv-point-data',
        filter: ['has', 'point_count'],
        paint: {
          'circle-color': [
            'step',
            ['get', 'point_count'],
            '#f59e0b',
            100,
            '#f97316',
            1000,
            '#dc2626',
          ],
          'circle-radius': [
            'step',
            ['get', 'point_count'],
            14,
            100,
            18,
            1000,
            24,
          ],
          'circle-stroke-color': '#ffffff',
          'circle-stroke-width': 1.5,
          'circle-opacity': 0.9,
        },
      });
    }

    if (!map.getLayer('csv-point-cluster-count')) {
      map.addLayer({
        id: 'csv-point-cluster-count',
        type: 'symbol',
        source: 'csv-point-data',
        filter: ['has', 'point_count'],
        layout: {
          'text-field': '{point_count_abbreviated}',
          'text-font': ['Open Sans Bold'],
          'text-size': 11,
        },
        paint: {
          'text-color': '#ffffff',
        },
      });
    }

    if (!map.getLayer('csv-point-unclustered')) {
      map.addLayer({
        id: 'csv-point-unclustered',
        type: 'circle',
        source: 'csv-point-data',
        filter: ['!', ['has', 'point_count']],
        paint: {
          'circle-radius': 3.5,
          'circle-color': '#dc2626',
          'circle-stroke-color': '#ffffff',
          'circle-stroke-width': 1,
          'circle-opacity': 0.85,
        },
      });
    }

    void refreshStateBoundarySource(map);

    const dataSource = map.getSource('geojson-data') as GeoJSONSource | undefined;
    dataSource?.setData(withPolygonColors(displayDataRef.current, polygonColorByIdRef.current));
    const csvPointSource = map.getSource('csv-point-data') as GeoJSONSource | undefined;
    csvPointSource?.setData(csvPointDataRef.current);
    clearHoveredFeature(map);

    if (selectedFeatureIdRef.current) {
      map.setFeatureState(
        {
          source: 'geojson-data',
          id: selectedFeatureIdRef.current,
        },
        { selected: true },
      );
    }

    map.setLayoutProperty('state-boundaries-line', 'visibility', showStatesRef.current ? 'visible' : 'none');
  }

  useEffect(() => {
    if (!mapContainerRef.current || mapRef.current) {
      return;
    }

    const map = new maplibregl.Map({
      container: mapContainerRef.current,
      style: BASEMAP_STYLE,
      center: [-96, 38],
      zoom: 3,
    });

    map.addControl(new maplibregl.NavigationControl(), 'top-right');

    map.on('style.load', () => {
      ensureMapDataLayers(map);

      if (pendingFitBoundsRef.current) {
        fitMapToBounds(pendingFitBoundsRef.current);
      }
    });

    map.on('click', 'csv-point-clusters', (event) => {
      const clusterFeature = event.features?.[0];
      if (!clusterFeature || clusterFeature.geometry?.type !== 'Point') {
        return;
      }

      const clusterIdValue = clusterFeature.properties?.cluster_id;
      const clusterId = typeof clusterIdValue === 'number' ? clusterIdValue : Number(clusterIdValue);
      if (!Number.isFinite(clusterId)) {
        return;
      }

      const coordinates = clusterFeature.geometry.coordinates;

      const source = map.getSource('csv-point-data') as GeoJSONSource | undefined;
      if (!source) {
        return;
      }

      void source.getClusterExpansionZoom(clusterId).then((zoom) => {
        map.easeTo({
          center: [coordinates[0], coordinates[1]],
          zoom,
          duration: 400,
        });
      });
    });

    map.on('mouseenter', 'csv-point-clusters', () => {
      map.getCanvas().style.cursor = 'pointer';
    });

    map.on('mouseleave', 'csv-point-clusters', () => {
      map.getCanvas().style.cursor = '';
    });

    map.on('mouseenter', 'csv-point-unclustered', () => {
      map.getCanvas().style.cursor = 'pointer';
    });

    map.on('mouseleave', 'csv-point-unclustered', () => {
      map.getCanvas().style.cursor = '';
    });

    map.on('click', (event) => {
      if (!map.getLayer('geojson-fill')) {
        closeContextMenu();
        return;
      }

      const hits = map.queryRenderedFeatures(event.point, { layers: ['geojson-fill'] });
      const appFeatureId = hits[0]?.properties?.appFeatureId;

      if (!appFeatureId || typeof appFeatureId !== 'string') {
        closeContextMenu();
        return;
      }

      const currentName = polygonNameByIdRef.current[appFeatureId] || 'Polygon';

      if (selectedFeatureIdRef.current === appFeatureId) {
        clearSelectedFeature(map);
        closeContextMenu();
        closePolygonMenu();
        return;
      }

      setContextMenu({
        open: true,
        x: event.point.x,
        y: event.point.y,
        appFeatureId,
        nameDraft: currentName,
      });
      setSelectedFeature(map, appFeatureId);
      closePolygonMenu();
    });

    map.on('mousemove', (event) => {
      if (!map.getLayer('geojson-fill')) {
        map.getCanvas().style.cursor = '';
        return;
      }

      const hits = map.queryRenderedFeatures(event.point, { layers: ['geojson-fill'] });
      const nextId = hits[0]?.properties?.appFeatureId;
      const nextFeatureId = typeof nextId === 'string' ? nextId : null;

      setHoveredFeature(map, nextFeatureId);
      map.getCanvas().style.cursor = nextFeatureId ? 'pointer' : '';
    });

    map.on('mouseleave', () => {
      clearHoveredFeature(map);
      map.getCanvas().style.cursor = '';
    });

    mapRef.current = map;

    return () => {
      clearHoveredFeature(map);
      clearSelectedFeature(map);
      map.remove();
      mapRef.current = null;
    };
  }, []);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded()) {
      return;
    }

    const source = map.getSource('geojson-data') as GeoJSONSource | undefined;
    source?.setData(withPolygonColors(smoothPreviewData, polygonColorByIdRef.current));
    clearHoveredFeature(map);
  }, [smoothPreviewData]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded()) {
      return;
    }

    const source = map.getSource('csv-point-data') as GeoJSONSource | undefined;
    source?.setData(csvPointData);
  }, [csvPointData]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded()) {
      return;
    }

    closeContextMenu();
    closePolygonMenu();
  }, [displayData]);

  useEffect(() => {
    const map = mapRef.current;
    if (!map?.isStyleLoaded() || !map.getLayer('state-boundaries-line')) {
      return;
    }

    map.setLayoutProperty('state-boundaries-line', 'visibility', showStates ? 'visible' : 'none');
  }, [showStates]);

  useEffect(() => {
    function handleKeyDown(event: KeyboardEvent) {
      if (!event.metaKey || shouldIgnoreHistoryShortcut(event.target)) {
        return;
      }

      const key = event.key.toLowerCase();
      if (key !== 'z') {
        return;
      }

      event.preventDefault();

      if (event.shiftKey) {
        handleRedo();
        return;
      }

      handleUndo();
    }

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [undoStack, redoStack, displayData, csvPointData, csvPointFiles, uploadedFiles, polygonNames]);

  async function importGeoJsonFiles(selectedFiles: File[]) {
    if (!selectedFiles.length) {
      return;
    }

    const importedFeatures: Feature<Geometry, GeoJsonProperties>[] = [];
    const importedFiles: UploadedFileMeta[] = [];
    const failedFiles: string[] = [];

    for (const selectedFile of selectedFiles) {
      try {
        const text = await selectedFile.text();
        const parsed = parseGeoJson(text);
        const fileId = `file-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
        const annotated = annotateImportedCollection(parsed, fileId, selectedFile.name);
        const polygonCount = annotated.features.filter((feature) => isPolygonFeature(feature)).length;

        importedFeatures.push(...annotated.features);
        importedFiles.push({
          id: fileId,
          name: selectedFile.name,
          featureCount: annotated.features.length,
          polygonCount,
        });
      } catch {
        failedFiles.push(selectedFile.name);
      }
    }

    if (importedFeatures.length > 0) {
      recordHistorySnapshot();
      setDisplayData((previous) => ({
        type: 'FeatureCollection',
        features: [...previous.features, ...importedFeatures],
      }));
      setUploadedFiles((previous) => [...previous, ...importedFiles]);

      fitMapToCollection({
        type: 'FeatureCollection',
        features: importedFeatures,
      });
    }

    if (failedFiles.length > 0) {
      setError(`Could not parse: ${failedFiles.join(', ')}`);
    } else {
      setError('');
    }

    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }
  }

  async function handleFileChange(event: React.ChangeEvent<HTMLInputElement>) {
    const selectedFiles = Array.from(event.target.files || []);
    await importGeoJsonFiles(selectedFiles);
  }

  async function importCsvPointFiles(selectedFiles: File[]) {
    if (!selectedFiles.length) {
      return;
    }

    const importedPointFeatures: Feature<Geometry, GeoJsonProperties>[] = [];
    const importedCsvFiles: CsvPointFileMeta[] = [];
    const failedFiles: string[] = [];
    let importedPointCount = 0;
    let skippedPointCount = 0;

    for (const selectedFile of selectedFiles) {
      try {
        const text = await selectedFile.text();
        const csvFileId = `csv-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
        const parsed = parseCsvPointCollection(text, selectedFile.name, csvFileId);
        importedPointFeatures.push(...parsed.data.features);
        importedCsvFiles.push({
          id: csvFileId,
          name: selectedFile.name,
          pointCount: parsed.importedCount,
        });
        importedPointCount += parsed.importedCount;
        skippedPointCount += parsed.skippedCount;
      } catch {
        failedFiles.push(selectedFile.name);
      }
    }

    if (importedPointFeatures.length > 0) {
      recordHistorySnapshot();
      const newCsvPointData: AnyFeatureCollection = {
        type: 'FeatureCollection',
        features: [...csvPointDataRef.current.features, ...importedPointFeatures],
      };
      setCsvPointData(newCsvPointData);
      setCsvPointFiles((previous) => [...previous, ...importedCsvFiles]);

      const map = mapRef.current;
      if (map) {
        const csvSource = map.getSource('csv-point-data') as GeoJSONSource | undefined;
        csvSource?.setData(newCsvPointData);
      }

      fitMapToCollection({
        type: 'FeatureCollection',
        features: importedPointFeatures,
      });

      setError('');
      setOperationAlert({
        type: 'success',
        message:
          skippedPointCount > 0
            ? `Imported ${importedPointCount} coordinate points from ${importedCsvFiles.length} CSV file${
                importedCsvFiles.length === 1 ? '' : 's'
              }. Skipped ${skippedPointCount} invalid row${skippedPointCount === 1 ? '' : 's'}.`
            : `Imported ${importedPointCount} coordinate points from ${importedCsvFiles.length} CSV file${
                importedCsvFiles.length === 1 ? '' : 's'
              }.`,
      });
    }

    if (failedFiles.length > 0) {
      const failureMessage = `Could not parse CSV file${failedFiles.length === 1 ? '' : 's'}: ${failedFiles.join(', ')}`;
      if (importedPointFeatures.length > 0) {
        setError('');
        setOperationAlert({
          type: 'error',
          message: failureMessage,
        });
      } else {
        setError(failureMessage);
      }
    }

    if (csvPointFileInputRef.current) {
      csvPointFileInputRef.current.value = '';
    }
  }

  async function handleCsvPointFileChange(event: React.ChangeEvent<HTMLInputElement>) {
    const selectedFiles = Array.from(event.target.files || []);
    await importCsvPointFiles(selectedFiles);
  }

  function handleCsvPointUploadClick() {
    csvPointFileInputRef.current?.click();
  }

  function handleCsvUploadDragEnter(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    csvUploadDragDepthRef.current += 1;
    setIsDragOverCsvUpload(true);
  }

  function handleCsvUploadDragOver(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    if (!isDragOverCsvUpload) {
      setIsDragOverCsvUpload(true);
    }
  }

  function handleCsvUploadDragLeave(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    csvUploadDragDepthRef.current = Math.max(0, csvUploadDragDepthRef.current - 1);
    if (csvUploadDragDepthRef.current === 0) {
      setIsDragOverCsvUpload(false);
    }
  }

  async function handleCsvUploadDrop(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    csvUploadDragDepthRef.current = 0;
    setIsDragOverCsvUpload(false);

    const droppedFiles = Array.from(event.dataTransfer.files || []);
    await importCsvPointFiles(droppedFiles);
  }

  function handleRemoveCsvPointFile(csvFileId: string) {
    recordHistorySnapshot();

    const newCsvPointData: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: csvPointDataRef.current.features.filter(
        (feature) => feature.properties?.csvSourceFileId !== csvFileId,
      ),
    };
    setCsvPointData(newCsvPointData);
    setCsvPointFiles((previous) => previous.filter((file) => file.id !== csvFileId));

    const map = mapRef.current;
    if (map) {
      const csvSource = map.getSource('csv-point-data') as GeoJSONSource | undefined;
      csvSource?.setData(newCsvPointData);
    }
  }

  function handleUploadDropZoneClick() {
    fileInputRef.current?.click();
  }

  function handleUploadDragEnter(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    uploadDragDepthRef.current += 1;
    setIsDragOverUpload(true);
  }

  function handleUploadDragOver(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    if (!isDragOverUpload) {
      setIsDragOverUpload(true);
    }
  }

  function handleUploadDragLeave(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    uploadDragDepthRef.current = Math.max(0, uploadDragDepthRef.current - 1);
    if (uploadDragDepthRef.current === 0) {
      setIsDragOverUpload(false);
    }
  }

  async function handleUploadDrop(event: React.DragEvent<HTMLDivElement>) {
    event.preventDefault();
    event.stopPropagation();
    uploadDragDepthRef.current = 0;
    setIsDragOverUpload(false);

    const droppedFiles = Array.from(event.dataTransfer.files || []);
    await importGeoJsonFiles(droppedFiles);
  }

  function handleRemoveFile(fileId: string) {
    const removedIds = new Set(
      displayData.features
        .filter((feature) => feature.properties?.sourceFileId === fileId)
        .map((feature) => String(feature.properties?.appFeatureId || '')),
    );

    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: previous.features.filter((feature) => feature.properties?.sourceFileId !== fileId),
    }));
    setUploadedFiles((previous) => previous.filter((file) => file.id !== fileId));
    closePolygonMenu();

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current && removedIds.has(selectedFeatureIdRef.current)) {
      clearSelectedFeature(map);
    }

    closeContextMenu();
  }

  function handleClearAll() {
    recordHistorySnapshot();
    setUploadedFiles([]);
    setDisplayData(EMPTY_COLLECTION);
    setCsvPointData(EMPTY_COLLECTION);
    setCsvPointFiles([]);
    setError('');
    setPolygonNames({});
    setMergeMode(false);
    setSelectedForMerge(new Set());
    closePolygonMenu();

    const map = mapRef.current;
    if (map) {
      clearSelectedFeature(map);
    }

    closeContextMenu();

    if (fileInputRef.current) {
      fileInputRef.current.value = '';
    }

    if (csvPointFileInputRef.current) {
      csvPointFileInputRef.current.value = '';
    }

    setIsDragOverUpload(false);
    setIsDragOverCsvUpload(false);
    uploadDragDepthRef.current = 0;
    csvUploadDragDepthRef.current = 0;
  }

  function toggleMergeMode() {
    setMergeMode((previous) => !previous);
    setSelectedForMerge(new Set());
    closePolygonMenu();
    closeSmoothPanel();
  }

  function toggleSelectForMerge(appFeatureId: string) {
    setSelectedForMerge((previous) => {
      const next = new Set(previous);
      if (next.has(appFeatureId)) {
        next.delete(appFeatureId);
      } else {
        next.add(appFeatureId);
      }
      return next;
    });
  }

  function handleMergeSelected() {
    if (selectedForMerge.size < 2) {
      return;
    }

    const featuresToMerge = displayData.features.filter(
      (feature) =>
        typeof feature.properties?.appFeatureId === 'string' &&
        selectedForMerge.has(feature.properties.appFeatureId) &&
        isPolygonFeature(feature as Feature<Geometry, GeoJsonProperties>),
    ) as Feature<Geometry, GeoJsonProperties>[];

    if (featuresToMerge.length < 2) {
      return;
    }

    const merged = mergePolygons(featuresToMerge as Parameters<typeof mergePolygons>[0]);
    if (!merged) {
      setError('Merge failed. Could not combine the selected polygons.');
      return;
    }

    const mergedIds = new Set(featuresToMerge.map((f) => f.properties?.appFeatureId as string));
    const firstSourceFileId = featuresToMerge[0]?.properties?.sourceFileId;
    const firstSourceFileName = featuresToMerge[0]?.properties?.sourceFileName;
    const newId = `merged-${Date.now()}`;
    const mergedNames = featuresToMerge
      .map((f) => polygonNameById[f.properties?.appFeatureId as string] || f.properties?.appFeatureId)
      .join(' + ');

    const stateNames = [
      ...new Set(
        featuresToMerge
          .map((f) => f.properties?.stateName)
          .filter((n): n is string => typeof n === 'string' && n.trim() !== ''),
      ),
    ];
    const anyWasSplit = featuresToMerge.some((f) => f.properties?.splitByState === true);

    const mergedFeature: Feature<Geometry, GeoJsonProperties> = {
      ...merged,
      properties: {
        ...merged.properties,
        appFeatureId: newId,
        sourceFileId: firstSourceFileId ?? 'merged',
        sourceFileName: firstSourceFileName ?? 'Merged',
        polygonName: mergedNames,
        splitByState: anyWasSplit,
        stateName: stateNames.length > 0 ? stateNames.join(', ') : undefined,
      },
    };

    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: [
        ...previous.features.filter(
          (feature) => !mergedIds.has(feature.properties?.appFeatureId as string),
        ),
        mergedFeature,
      ],
    }));

    setPolygonNames((previous) => ({
      ...previous,
      [newId]: mergedNames,
    }));

    setSelectedForMerge(new Set());
    setMergeMode(false);
    closeSmoothPanel();
    setError('');
  }

  async function handleSplitAll() {
    if (!displayData.features.length || isSplittingAll) {
      return;
    }

    setIsSplittingAll(true);
    setOperationAlert(null);
    await waitForUiPaint();

    try {
      const result = await splitPolygonsByStates(displayData);
      recordHistorySnapshot();
      setDisplayData(withFeatureIds(result.data, 'split-all'));
      setError('');
      const noIntersectionMessage =
        result.summary.noIntersectionCount > 0
          ? ` ${result.summary.noIntersectionCount} polygon${
              result.summary.noIntersectionCount === 1 ? '' : 's'
            } had no intersecting state boundaries.`
          : '';
      setOperationAlert({
        type: 'success',
        message:
          result.summary.splitCount > 0
            ? `Split complete. Created ${result.summary.splitCount} state pieces.${noIntersectionMessage}`
            : `Split complete. No state-boundary splits were needed.${noIntersectionMessage}`,
      });
    } catch {
      setError('Split failed. Could not split polygons by state.');
      setOperationAlert({
        type: 'error',
        message: 'Split failed. Could not split polygons by state.',
      });
    } finally {
      setIsSplittingAll(false);
    }
  }

  function handleSmoothAll() {
    if (!polygonItems.length) {
      return;
    }

    const smoothed = smoothPolygonsInCollection(displayData, {
      algorithm: 'simplify',
      sensitivity: 40,
    });
    recordHistorySnapshot();
    setDisplayData(smoothed);
    setError('');
  }

  function openSmoothPanelForFeature(appFeatureId: string, anchorElement?: HTMLElement) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target || !isPolygonFeature(target as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const rect = anchorElement?.getBoundingClientRect();
    const x = rect ? rect.right - 288 : 24;
    const y = rect ? rect.bottom + 8 : 28;

    setSmoothPanel({
      open: true,
      appFeatureId,
      algorithm: 'simplify',
      sensitivity: 40,
      x,
      y,
    });
  }

  function applySmoothToFeature() {
    if (!smoothPanel.appFeatureId) {
      return;
    }

    recordHistorySnapshot();
    setDisplayData(smoothPreviewData);

    setError('');
    closeSmoothPanel();
  }

  async function handleSplitFeatureById(appFeatureId: string) {
    if (splittingFeatureIds.has(appFeatureId)) {
      return;
    }

    const targetFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    if (!targetFeature || !isPolygonFeature(targetFeature)) {
      return;
    }

    setSplittingFeatureIds((previous) => {
      const next = new Set(previous);
      next.add(appFeatureId);
      return next;
    });
    setOperationAlert(null);
    await waitForUiPaint();

    try {
      const splitResult = await splitPolygonsByStates({
        type: 'FeatureCollection',
        features: [targetFeature],
      });

      if (splitResult.summary.noIntersectionCount > 0) {
        setError('');
        setOperationAlert({
          type: 'success',
          message: 'No state boundaries intersect with this polygon.',
        });
        return;
      }

      const splitFeatures = splitResult.data.features.map((feature, index) => ({
        ...feature,
        properties: {
          ...feature.properties,
          appFeatureId: `${appFeatureId}-piece-${Date.now()}-${index}`,
        },
      }));

      recordHistorySnapshot();
      setDisplayData((previous) => ({
        type: 'FeatureCollection',
        features: [
          ...previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
          ...splitFeatures,
        ],
      }));

      const map = mapRef.current;
      if (map && selectedFeatureIdRef.current === appFeatureId) {
        clearSelectedFeature(map);
      }

      closePolygonMenu();
      closeContextMenu();
      setError('');
      setOperationAlert({
        type: 'success',
        message:
          splitFeatures.length > 1
            ? `Split complete. Created ${splitFeatures.length} state pieces.`
            : 'Split complete. No additional state pieces were created.',
      });
    } catch {
      setError('Split failed. Could not split the selected polygon by state.');
      setOperationAlert({
        type: 'error',
        message: 'Split failed. Could not split the selected polygon by state.',
      });
    } finally {
      setSplittingFeatureIds((previous) => {
        const next = new Set(previous);
        next.delete(appFeatureId);
        return next;
      });
    }
  }

  function handleSeparatePartsById(appFeatureId: string) {
    const targetFeature = displayData.features.find(
      (feature) => feature.properties?.appFeatureId === appFeatureId,
    ) as Feature<Geometry, GeoJsonProperties> | undefined;

    if (!targetFeature || targetFeature.geometry?.type !== 'MultiPolygon') {
      return;
    }

    const separatedParts = separatePolygonParts(targetFeature as Parameters<typeof separatePolygonParts>[0]);
    if (separatedParts.length <= 1) {
      return;
    }

    const baseName = polygonNameById[appFeatureId] || getPolygonDefaultName(targetFeature, 0);
    const replacementFeatures = separatedParts.map((feature, index) => ({
      ...feature,
      properties: {
        ...feature.properties,
        appFeatureId: `${appFeatureId}-part-${Date.now()}-${index}`,
        polygonName: `${baseName} Part ${index + 1}`,
      },
    }));

    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: [
        ...previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
        ...replacementFeatures,
      ],
    }));

    setPolygonNames((previous) => {
      const next = { ...previous };
      delete next[appFeatureId];

      replacementFeatures.forEach((feature, index) => {
        const nextId = feature.properties?.appFeatureId;
        if (typeof nextId === 'string') {
          next[nextId] = `${baseName} Part ${index + 1}`;
        }
      });

      return next;
    });

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current === appFeatureId) {
      clearSelectedFeature(map);
    }

    closeSmoothPanel();
    closePolygonMenu();
    closeContextMenu();
    setError('');
  }

  function handleDeleteFeatureById(appFeatureId: string) {
    recordHistorySnapshot();
    setDisplayData((previous) => ({
      type: 'FeatureCollection',
      features: previous.features.filter((feature) => feature.properties?.appFeatureId !== appFeatureId),
    }));

    const map = mapRef.current;
    if (map && selectedFeatureIdRef.current === appFeatureId) {
      clearSelectedFeature(map);
    }

    closePolygonMenu();
    if (smoothPanel.appFeatureId === appFeatureId) {
      closeSmoothPanel();
    }
    closeContextMenu();
  }

  function handleFocusPolygon(appFeatureId: string) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target) {
      return;
    }

    const map = mapRef.current;
    if (selectedFeatureId === appFeatureId) {
      if (map) clearSelectedFeature(map);
      closePolygonMenu();
      return;
    }

    if (map) {
      setSelectedFeature(map, appFeatureId);
    }

    fitMapToCollection({
      type: 'FeatureCollection',
      features: [target],
    });
    closePolygonMenu();
  }

  function handlePolygonNameChange(appFeatureId: string, name: string) {
    recordHistorySnapshot();
    setPolygonNames((previous) => ({
      ...previous,
      [appFeatureId]: name,
    }));
  }

  function startPolygonNameEdit(appFeatureId: string) {
    setCollapsedPolygonIds((previous) => {
      if (!previous.has(appFeatureId)) {
        return previous;
      }

      const next = new Set(previous);
      next.delete(appFeatureId);
      return next;
    });
    setEditingPolygonId(appFeatureId);
    setEditingPolygonNameDraft(polygonNameById[appFeatureId] || '');
  }

  function cancelPolygonNameEdit() {
    setEditingPolygonId(null);
    setEditingPolygonNameDraft('');
  }

  function savePolygonNameEdit(appFeatureId: string) {
    handlePolygonNameChange(appFeatureId, editingPolygonNameDraft);
    setEditingPolygonId(null);
    setEditingPolygonNameDraft('');
  }

  function handleExportPolygon(appFeatureId: string) {
    const target = displayData.features.find((feature) => feature.properties?.appFeatureId === appFeatureId);
    if (!target || !isPolygonFeature(target as Feature<Geometry, GeoJsonProperties>)) {
      return;
    }

    const targetName = polygonNameById[appFeatureId] || 'polygon';
    const fileNameStem = sanitizeFileName(targetName);
    const payload: AnyFeatureCollection = {
      type: 'FeatureCollection',
      features: [
        {
          ...target,
          properties: {
            ...target.properties,
            polygonName: targetName,
          },
        },
      ],
    };

    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/geo+json' });
    const href = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = href;
    link.download = `${fileNameStem || 'polygon'}.geojson`;
    link.click();
    URL.revokeObjectURL(href);
  }

  function handleSaveContextMenuRename() {
    if (!contextMenu.appFeatureId) {
      return;
    }

    handlePolygonNameChange(contextMenu.appFeatureId, contextMenu.nameDraft);
    closeContextMenu();
  }

  return (
    <div className="flex h-full min-h-screen bg-[#f2f4f7] text-slate-900">
      <aside className="flex w-full max-w-107.5 flex-col border-r border-slate-200 bg-linear-to-b from-[#fffdf8] to-[#f3f5ff] p-5 lg:p-6">
        <div className="mb-5">
          <p className="flex items-center gap-1.5 text-xs font-semibold uppercase tracking-[0.25em] text-orange-700">
            <Braces className="h-3.5 w-3.5" />
            GeoJSON Workspace
          </p>
          <h1 className="mt-3 text-4xl font-black leading-[0.92] tracking-tight text-slate-900">
            Multi-file polygon operations.
          </h1>
          <p className="mt-3 text-sm text-slate-600">
            Upload multiple files and manage each polygon independently in the list or directly on the map.
          </p>
        </div>

        <section className="space-y-3 rounded-2xl border border-slate-200 bg-white/85 p-4 shadow-sm">
          <label className="flex items-center gap-1.5 text-xs font-semibold uppercase tracking-wide text-slate-600">
            <FileUp className="h-3.5 w-3.5" />
            Upload GeoJSON Files
          </label>
          <div
            role="button"
            tabIndex={0}
            onClick={handleUploadDropZoneClick}
            onKeyDown={(event) => {
              if (event.key === 'Enter' || event.key === ' ') {
                event.preventDefault();
                handleUploadDropZoneClick();
              }
            }}
            onDragEnter={handleUploadDragEnter}
            onDragOver={handleUploadDragOver}
            onDragLeave={handleUploadDragLeave}
            onDrop={handleUploadDrop}
            className={`group block cursor-pointer rounded-xl border-2 border-dashed p-4 transition ${
              isDragOverUpload
                ? 'border-indigo-500 bg-indigo-100/60 ring-2 ring-indigo-200'
                : 'border-slate-300 bg-slate-50/70 hover:border-indigo-400 hover:bg-indigo-50/50'
            }`}
          >
            <div className="flex items-start gap-3">
              <div
                className={`rounded-lg bg-white p-2 text-slate-700 shadow-sm ring-1 ring-slate-200 transition ${
                  isDragOverUpload ? 'scale-105 text-indigo-700 ring-indigo-300' : ''
                }`}
              >
                <FileUp className="h-5 w-5" />
              </div>
              <div>
                <p className={`text-sm font-semibold ${isDragOverUpload ? 'text-indigo-800' : 'text-slate-800'}`}>
                  {isDragOverUpload ? 'Release to upload files' : 'Drop GeoJSON files here'}
                </p>
                <p className={`text-xs ${isDragOverUpload ? 'text-indigo-700' : 'text-slate-500'}`}>
                  {isDragOverUpload
                    ? 'Files will be imported and mapped immediately'
                    : 'or click to browse .geojson and .json files'}
                </p>
              </div>
            </div>
          </div>
          <input
            ref={fileInputRef}
            type="file"
            multiple
            accept=".json,.geojson,application/geo+json,application/json"
            onChange={handleFileChange}
            className="hidden"
          />

          <div
            role="button"
            tabIndex={0}
            onClick={handleCsvPointUploadClick}
            onKeyDown={(event) => {
              if (event.key === 'Enter' || event.key === ' ') {
                event.preventDefault();
                handleCsvPointUploadClick();
              }
            }}
            onDragEnter={handleCsvUploadDragEnter}
            onDragOver={handleCsvUploadDragOver}
            onDragLeave={handleCsvUploadDragLeave}
            onDrop={handleCsvUploadDrop}
            className={`group block cursor-pointer rounded-xl border-2 border-dashed p-4 transition ${
              isDragOverCsvUpload
                ? 'border-indigo-500 bg-indigo-100/60 ring-2 ring-indigo-200'
                : 'border-slate-300 bg-slate-50/70 hover:border-indigo-400 hover:bg-indigo-50/50'
            }`}
          >
            <div className="flex items-start gap-3">
              <div
                className={`rounded-lg bg-white p-2 text-slate-700 shadow-sm ring-1 ring-slate-200 transition ${
                  isDragOverCsvUpload ? 'scale-105 text-indigo-700 ring-indigo-300' : ''
                }`}
              >
                <MapPinned className="h-5 w-5" />
              </div>
              <div>
                <p className={`text-sm font-semibold ${isDragOverCsvUpload ? 'text-indigo-800' : 'text-slate-800'}`}>
                  {isDragOverCsvUpload ? 'Release to upload files' : 'Drop CSV files here'}
                </p>
                <p className={`text-xs ${isDragOverCsvUpload ? 'text-indigo-700' : 'text-slate-500'}`}>
                  {isDragOverCsvUpload
                    ? 'Files will be imported and mapped immediately'
                    : 'or click to browse coordinate files with lat/lon columns'}
                </p>
              </div>
            </div>

            <input
              ref={csvPointFileInputRef}
              type="file"
              multiple
              accept=".csv,text/csv"
              onChange={handleCsvPointFileChange}
              className="hidden"
            />

            {csvPointFiles.length > 0 ? (
              <div className="mt-2 max-h-24 space-y-1 overflow-y-auto pr-1">
                {csvPointFiles.map((csvFile) => (
                  <div key={csvFile.id} className="flex items-center justify-between rounded-md bg-white px-2 py-1 ring-1 ring-slate-200">
                    <p className="truncate text-[11px] font-medium text-slate-700" title={csvFile.name}>
                      {csvFile.name} ({csvFile.pointCount.toLocaleString()} pts)
                    </p>
                    <button
                      type="button"
                      onClick={(event) => {
                        event.stopPropagation();
                        handleRemoveCsvPointFile(csvFile.id);
                      }}
                      aria-label={`Remove ${csvFile.name}`}
                      title={`Remove ${csvFile.name}`}
                      className="ml-2 inline-flex h-6 w-6 shrink-0 items-center justify-center rounded-md text-red-600 transition hover:bg-red-50"
                    >
                      <Trash2 className="h-3.5 w-3.5" />
                    </button>
                  </div>
                ))}
              </div>
            ) : null}
          </div>

          <div className="flex items-center justify-between rounded-lg border border-slate-200 bg-slate-50 px-3 py-2">
            <span className="inline-flex items-center gap-1.5 text-sm font-medium text-slate-700">
              <MapPinned className="h-4 w-4" />
              Show state boundaries
            </span>
            <button
              type="button"
              role="switch"
              aria-checked={showStates}
              onClick={() => setShowStates((previous) => !previous)}
              className={`relative h-7 w-12 rounded-full transition ${showStates ? 'bg-slate-900' : 'bg-slate-300'}`}
            >
              <span
                className={`absolute top-1 h-5 w-5 rounded-full bg-white transition ${showStates ? 'left-6' : 'left-1'}`}
              />
            </button>
          </div>

          {error ? <p className="text-sm font-semibold text-red-700">{error}</p> : null}
          {isSplittingAll || splittingFeatureIds.size > 0 ? (
            <p role="status" className="text-sm font-semibold text-indigo-700">
              Splitting polygons by state boundaries...
            </p>
          ) : null}
          {operationAlert ? (
            <p
              role="alert"
              className={`text-sm font-semibold ${
                operationAlert.type === 'success' ? 'text-emerald-700' : 'text-red-700'
              }`}
            >
              {operationAlert.message}
            </p>
          ) : null}
        </section>

        <section className="mt-4 flex min-h-0 flex-1 flex-col rounded-2xl border border-slate-200 bg-white/85 p-4 shadow-sm">
          <div className="flex flex-wrap items-start justify-between gap-3">
            <div>
              <h2 className="inline-flex items-center gap-1.5 text-sm font-bold uppercase tracking-wide text-slate-700">
                <FolderTree className="h-4 w-4" />
                Files and Polygons
              </h2>
              <p className="mt-1 text-xs text-slate-500">Split, rename, export, or remove polygons by file.</p>
            </div>

            <div className="flex w-full gap-2">
              <ToolbarActionButton
                onClick={handleUndo}
                disabled={!undoStack.length}
                ariaLabel="Undo"
                tooltip="Undo (Cmd+Z)"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-slate-300 bg-white text-slate-700 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:border-slate-200 disabled:bg-slate-100 disabled:text-slate-400"
              >
                <Undo2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleRedo}
                disabled={!redoStack.length}
                ariaLabel="Redo"
                tooltip="Redo (Cmd+Shift+Z)"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg border border-slate-300 bg-white text-slate-700 transition hover:bg-slate-50 disabled:cursor-not-allowed disabled:border-slate-200 disabled:bg-slate-100 disabled:text-slate-400"
              >
                <Redo2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleSplitAll}
                disabled={!polygonItems.length || isSplittingAll || splittingFeatureIds.size > 0}
                ariaLabel={isSplittingAll || splittingFeatureIds.size > 0 ? 'Splitting polygons' : 'Split All by State'}
                tooltip={isSplittingAll || splittingFeatureIds.size > 0 ? 'Splitting...' : 'Split All by State'}
                className="inline-flex h-9 w-full items-center justify-center rounded-lg bg-slate-900 text-white transition hover:bg-slate-700 disabled:cursor-not-allowed disabled:bg-slate-300"
              >
                {isSplittingAll || splittingFeatureIds.size > 0 ? (
                  <Loader2 className="h-4 w-4 animate-spin" />
                ) : (
                  <Scissors className="h-4 w-4" />
                )}
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleClearAll}
                disabled={!uploadedFiles.length && !csvPointData.features.length}
                ariaLabel="Clear All Files"
                tooltip="Clear All Files"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg bg-red-600 text-white transition hover:bg-red-500 disabled:cursor-not-allowed disabled:bg-red-200"
              >
                <Trash2 className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={handleSmoothAll}
                disabled={!polygonItems.length}
                ariaLabel="Simplify All Polygons"
                tooltip="Simplify All Polygons"
                className="inline-flex h-9 w-full items-center justify-center rounded-lg bg-teal-100 text-teal-800 transition hover:bg-teal-200 disabled:cursor-not-allowed disabled:bg-slate-100 disabled:text-slate-400"
              >
                <PenLine className="h-4 w-4" />
              </ToolbarActionButton>
              <ToolbarActionButton
                onClick={toggleMergeMode}
                disabled={polygonItems.length < 2}
                ariaLabel={mergeMode ? 'Cancel Merge' : 'Merge Polygons'}
                tooltip={mergeMode ? 'Cancel Merge' : 'Merge Polygons'}
                className={`inline-flex h-9 w-full items-center justify-center rounded-lg transition disabled:cursor-not-allowed ${
                  mergeMode
                    ? 'bg-violet-700 text-white hover:bg-violet-600 disabled:bg-violet-300'
                    : 'bg-violet-100 text-violet-800 hover:bg-violet-200 disabled:bg-slate-100 disabled:text-slate-400'
                }`}
              >
                {mergeMode ? <X className="h-4 w-4" /> : <Merge className="h-4 w-4" />}
              </ToolbarActionButton>
            </div>
          </div>

          {mergeMode && (
            <div className="mt-3 flex items-center justify-between rounded-lg border border-violet-200 bg-violet-50 px-3 py-2">
              <span className="text-xs text-violet-700">
                {selectedForMerge.size < 2
                  ? `Select ${2 - selectedForMerge.size} more polygon${selectedForMerge.size === 1 ? '' : 's'}`
                  : `${selectedForMerge.size} polygons selected`}
              </span>
              <button
                onClick={handleMergeSelected}
                disabled={selectedForMerge.size < 2}
                className="inline-flex items-center gap-1 rounded-md bg-violet-700 px-2.5 py-1.5 text-xs font-semibold text-white transition hover:bg-violet-600 disabled:cursor-not-allowed disabled:bg-violet-300"
              >
                <Merge className="h-3.5 w-3.5" />
                Merge {selectedForMerge.size > 0 ? selectedForMerge.size : ''} Selected
              </button>
            </div>
          )}

          <div className="mt-3 space-y-3 overflow-y-auto pr-1">
            {filesWithPolygons.length === 0 ? (
              <p className="flex h-full w-full rounded-lg items-center justify-center border border-dashed border-slate-300 bg-slate-50 p-3 text-sm text-slate-500">
                No files loaded yet.
              </p>
            ) : (
              filesWithPolygons.map((group) => (
                <article key={group.id} className="rounded-xl border border-slate-200 bg-slate-50 p-3 overflow-visible">
                  <div className="mb-3 flex items-start justify-between gap-2">
                    <div>
                      <p className="max-w-55 truncate text-sm font-bold text-slate-900">{group.name}</p>
                      <p className="text-xs text-slate-500">
                        {group.featureCount} features, {group.polygons.length} polygons currently visible
                      </p>
                    </div>
                    <button
                      onClick={() => handleRemoveFile(group.id)}
                      className="inline-flex items-center gap-1 rounded-lg border border-red-200 bg-red-50 p-2 text-xs font-semibold text-red-700 transition hover:bg-red-200"
                    >
                      <Trash2 className="h-3.5 w-3.5" />
                    </button>
                  </div>

                  <div className="space-y-2">
                    {group.polygons.length === 0 ? (
                      <p className="flex h-full w-full rounded-lg items-center justify-center border border-dashed border-slate-300 bg-white p-2 text-xs text-slate-500">
                        No polygons from this file are currently visible.
                      </p>
                    ) : (
                      group.polygons.map((item, index) => {
                        const isChecked = selectedForMerge.has(item.appFeatureId);
                        const isSelected = !mergeMode && selectedFeatureId === item.appFeatureId;
                        const isSplitBusy = splittingFeatureIds.has(item.appFeatureId);
                        const isCollapsed = collapsedPolygonIds.has(item.appFeatureId);
                        const metrics = polygonMetricsById[item.appFeatureId] || { vertices: 0, edges: 0 };
                        const polygonColor = isSelected
                          ? POLYGON_SELECTED_FILL_COLOR
                          : polygonColorById[item.appFeatureId] || getPolygonColorForId(item.appFeatureId);
                        return (
                        <div
                          key={item.appFeatureId}
                          data-appfeatureid={item.appFeatureId}
                          onClick={() => mergeMode ? toggleSelectForMerge(item.appFeatureId) : handleFocusPolygon(item.appFeatureId)}
                          className={`relative rounded-lg border p-2.5 transition ${
                            mergeMode && isChecked
                              ? 'border-violet-400 bg-violet-50 ring-1 ring-violet-300'
                              : isSelected
                              ? 'border-amber-400 bg-amber-50 ring-1 ring-amber-300'
                              : 'border-slate-200 bg-white hover:border-indigo-300 hover:bg-indigo-50/40'
                          } ${mergeMode ? 'cursor-pointer' : ''}`}
                        >
                          <div className="flex items-center justify-between gap-2">
                            {mergeMode ? (
                              <div className="flex items-center gap-2">
                                <input
                                  type="checkbox"
                                  checked={isChecked}
                                  onChange={() => toggleSelectForMerge(item.appFeatureId)}
                                  onClick={(event) => event.stopPropagation()}
                                  className="h-4 w-4 cursor-pointer accent-violet-700"
                                />
                                <p className="inline-flex items-center gap-1 truncate text-[11px] font-semibold uppercase tracking-wide text-violet-700">
                                  <Tag className="h-3 w-3" />
                                  Polygon {index + 1}
                                </p>
                              </div>
                            ) : (
                              <div className="flex items-center gap-1">
                                <span
                                  aria-hidden="true"
                                  className="h-2.5 w-2.5 rounded-full ring-1 ring-slate-300"
                                  style={{ backgroundColor: polygonColor }}
                                />
                                <p className="truncate text-[11px] font-semibold uppercase tracking-wide text-slate-500">
                                  Polygon {index + 1}
                                </p>
                                {editingPolygonId !== item.appFeatureId ? (
                                  <button
                                    onClick={(event) => {
                                      event.stopPropagation();
                                      startPolygonNameEdit(item.appFeatureId);
                                    }}
                                    title="Edit polygon name"
                                    aria-label="Edit polygon name"
                                    className="inline-flex p-1 items-center justify-center rounded-md text-slate-500 transition hover:bg-slate-100 hover:text-slate-700"
                                  >
                                    <Pencil className="h-3 w-3" />
                                  </button>
                                ) : null}
                              </div>
                            )}
                            {item.splitByState && item.stateBadge ? (
                              <span className="rounded-full bg-orange-100 px-2 py-0.5 text-[10px] font-bold uppercase tracking-wide text-orange-700">
                                {item.stateBadge}
                              </span>
                            ) : null}

                            {!mergeMode && (
                              <div className="ml-auto flex items-center gap-1" onClick={(event) => event.stopPropagation()}>
                                <PolygonIconActionButton
                                  onClick={() => void handleSplitFeatureById(item.appFeatureId)}
                                  tooltip={isSplitBusy ? 'Splitting...' : 'Split by State'}
                                  ariaLabel={isSplitBusy ? 'Splitting polygon by state' : 'Split by State'}
                                  disabled={isSplitBusy}
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-indigo-200 bg-indigo-50 text-indigo-700 transition hover:bg-indigo-100"
                                >
                                  {isSplitBusy ? <Loader2 className="h-3 w-3 animate-spin" /> : <Scissors className="h-3 w-3" />}
                                </PolygonIconActionButton>
                                {item.isMultiPolygon ? (
                                  <PolygonIconActionButton
                                    onClick={() => handleSeparatePartsById(item.appFeatureId)}
                                    tooltip="Separate Parts"
                                    ariaLabel="Separate Parts"
                                    className="inline-flex p-1 items-center justify-center rounded-md border border-sky-200 bg-sky-50 text-sky-700 transition hover:bg-sky-100"
                                  >
                                    <Braces className="h-3 w-3" />
                                  </PolygonIconActionButton>
                                ) : null}
                                <PolygonIconActionButton
                                  onClick={() => handleExportPolygon(item.appFeatureId)}
                                  tooltip="Export"
                                  ariaLabel="Export"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-emerald-200 bg-emerald-50 text-emerald-700 transition hover:bg-emerald-100"
                                >
                                  <Download className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={(event) => openSmoothPanelForFeature(item.appFeatureId, event.currentTarget)}
                                  tooltip="Smooth"
                                  ariaLabel="Smooth"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-teal-200 bg-teal-50 text-teal-700 transition hover:bg-teal-100"
                                >
                                  <PenLine className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={() => handleDeleteFeatureById(item.appFeatureId)}
                                  tooltip="Remove"
                                  ariaLabel="Remove"
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-red-200 bg-red-50 text-red-700 transition hover:bg-red-100"
                                >
                                  <Trash2 className="h-3 w-3" />
                                </PolygonIconActionButton>
                                <PolygonIconActionButton
                                  onClick={() => togglePolygonExpanded(item.appFeatureId)}
                                  tooltip={isCollapsed ? 'Expand Details' : 'Collapse Details'}
                                  ariaLabel={isCollapsed ? 'Expand polygon details' : 'Collapse polygon details'}
                                  className="inline-flex p-1 items-center justify-center rounded-md border border-slate-200 bg-slate-50 text-slate-700 transition hover:bg-slate-100"
                                >
                                  {isCollapsed ? <ChevronDown className="h-3 w-3" /> : <ChevronUp className="h-3 w-3" />}
                                </PolygonIconActionButton>
                              </div>
                            )}
                          </div>

                          <AnimatePresence initial={false}>
                            {!isCollapsed ? (
                              <motion.div
                                key={`details-${item.appFeatureId}`}
                                initial={{ height: 0, opacity: 0 }}
                                animate={{ height: 'auto', opacity: 1 }}
                                exit={{ height: 0, opacity: 0 }}
                                transition={{ duration: 0.2, ease: 'easeInOut' }}
                                className="overflow-hidden"
                              >
                              <div className="mt-1 flex items-center gap-1" onClick={(event) => event.stopPropagation()}>
                                {editingPolygonId === item.appFeatureId ? (
                                  <>
                                    <input
                                      value={editingPolygonNameDraft}
                                      onChange={(event) => setEditingPolygonNameDraft(event.target.value)}
                                      onClick={(event) => event.stopPropagation()}
                                      className="w-full rounded-lg border border-slate-300 bg-white px-2.5 py-2 text-sm text-slate-900"
                                      placeholder="Polygon name"
                                    />
                                    <button
                                      onClick={(event) => {
                                        event.stopPropagation();
                                        savePolygonNameEdit(item.appFeatureId);
                                      }}
                                      title="Save name"
                                      aria-label="Save name"
                                      className="inline-flex p-2 items-center justify-center rounded-md bg-emerald-600 text-white transition hover:bg-emerald-500"
                                    >
                                      <Check className="h-4.5 w-4.5" />
                                    </button>
                                    <button
                                      onClick={(event) => {
                                        event.stopPropagation();
                                        cancelPolygonNameEdit();
                                      }}
                                      title="Cancel rename"
                                      aria-label="Cancel rename"
                                      className="inline-flex p-2 items-center justify-center rounded-md border border-slate-300 text-slate-700 transition hover:bg-slate-50"
                                    >
                                      <X className="h-4.5 w-4.5" />
                                    </button>
                                  </>
                                ) : (
                                  <p className="w-full mt-2 truncate rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2 text-sm text-slate-700">
                                    {polygonNameById[item.appFeatureId] || item.defaultName}
                                  </p>
                                )}
                              </div>

                              <div className="mt-2 grid grid-cols-2 gap-2" onClick={(event) => event.stopPropagation()}>
                                <div className="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2">
                                  <p className="text-[10px] font-semibold uppercase tracking-wide text-slate-500">Vertices</p>
                                  <p className="mt-0.5 text-sm font-bold text-slate-800">{metrics.vertices}</p>
                                </div>
                                <div className="rounded-lg border border-slate-200 bg-slate-50 px-2.5 py-2">
                                  <p className="text-[10px] font-semibold uppercase tracking-wide text-slate-500">Edges</p>
                                  <p className="mt-0.5 text-sm font-bold text-slate-800">{metrics.edges}</p>
                                </div>
                              </div>
                              </motion.div>
                            ) : null}
                          </AnimatePresence>
                        </div>
                        );
                      })
                    )}
                  </div>
                </article>
              ))
            )}
          </div>
        </section>
      </aside>

      {smoothPanel.open ? (
        <div className="fixed inset-0 z-35" onClick={closeSmoothPanel}>
          <div
            className="absolute w-72 rounded-xl border border-slate-300 bg-white p-3 shadow-2xl"
            style={{
              left: `${Math.min(smoothPanel.x, window.innerWidth - 304)}px`,
              top: `${Math.min(smoothPanel.y, window.innerHeight - 260)}px`,
            }}
            onClick={(event) => event.stopPropagation()}
          >
            <p className="text-xs font-bold uppercase tracking-wide text-slate-500">Polygon Geometry</p>
            <p className="mt-1 text-xs text-slate-600">Preview shape changes live. Apply commits them.</p>

            <label className="mt-3 block text-[11px] font-semibold uppercase tracking-wide text-slate-500">
              Algorithm
            </label>
            <select
              value={smoothPanel.algorithm}
              onChange={(event) =>
                setSmoothPanel((previous) => ({
                  ...previous,
                  algorithm: event.target.value as SmoothAlgorithm,
                }))
              }
              className="mt-1 w-full rounded-md border border-slate-300 bg-white px-2 py-1.5 text-sm text-slate-800"
            >
              <option value="simplify">Simplify (reduce vertices)</option>
              <option value="chaikin">Chaikin (corner-cutting)</option>
              <option value="moving-average">Moving average</option>
              <option value="midpoint-subdivide">Midpoint subdivide</option>
            </select>

            <div className="mt-3">
              <div className="flex items-center justify-between text-[11px] font-semibold uppercase tracking-wide text-slate-500">
                <span>{smoothPanel.algorithm === 'simplify' ? 'Simplify Amount' : 'Sensitivity'}</span>
                <span>{smoothPanel.sensitivity}</span>
              </div>
              <input
                type="range"
                min={0}
                max={100}
                step={1}
                value={smoothPanel.sensitivity}
                onChange={(event) =>
                  setSmoothPanel((previous) => ({
                    ...previous,
                    sensitivity: Number(event.target.value),
                  }))
                }
                className="mt-1 w-full accent-teal-600"
              />
              <p className="mt-1 text-[11px] text-slate-500">
                {smoothPanel.algorithm === 'simplify'
                  ? 'Higher values remove more vertices.'
                  : 'Higher values create a stronger smoothing effect.'}
              </p>

              {smoothGeometryMetrics ? (
                <div className="mt-3 grid grid-cols-2 gap-2 text-[11px]">
                  <div className="rounded-md border border-slate-200 bg-slate-50 px-2 py-1.5">
                    <p className="font-semibold uppercase tracking-wide text-slate-500">Vertices</p>
                    <p className="text-sm font-bold text-slate-800">
                      {smoothGeometryMetrics.preview.vertices}
                      <span className="ml-1 text-[11px] font-medium text-slate-500">
                        ({smoothGeometryMetrics.preview.vertices - smoothGeometryMetrics.original.vertices >= 0
                          ? '+'
                          : ''}
                        {smoothGeometryMetrics.preview.vertices - smoothGeometryMetrics.original.vertices})
                      </span>
                    </p>
                  </div>
                  <div className="rounded-md border border-slate-200 bg-slate-50 px-2 py-1.5">
                    <p className="font-semibold uppercase tracking-wide text-slate-500">Edges</p>
                    <p className="text-sm font-bold text-slate-800">
                      {smoothGeometryMetrics.preview.edges}
                      <span className="ml-1 text-[11px] font-medium text-slate-500">
                        ({smoothGeometryMetrics.preview.edges - smoothGeometryMetrics.original.edges >= 0
                          ? '+'
                          : ''}
                        {smoothGeometryMetrics.preview.edges - smoothGeometryMetrics.original.edges})
                      </span>
                    </p>
                  </div>
                </div>
              ) : null}
            </div>

            <div className="mt-4 flex justify-end gap-2">
              <button
                onClick={closeSmoothPanel}
                className="rounded-md border border-slate-300 px-2.5 py-1.5 text-xs font-semibold text-slate-700 transition hover:bg-slate-50"
              >
                Cancel
              </button>
              <button
                onClick={applySmoothToFeature}
                className="rounded-md bg-teal-600 px-2.5 py-1.5 text-xs font-semibold text-white transition hover:bg-teal-500"
              >
                Apply Smoothing
              </button>
            </div>
          </div>
        </div>
      ) : null}

      <main className="relative flex-1 p-3 lg:p-4">
        <div
          ref={mapContainerRef}
          className="h-[58vh] w-full overflow-hidden rounded-3xl border border-slate-200 shadow-[0_28px_70px_rgba(15,23,42,0.18)] lg:h-[calc(100vh-2rem)]"
        />

        {contextMenu.open ? (
          <div
            className="absolute z-20 grid min-w-65 gap-2 rounded-xl border border-slate-300 bg-white p-2 shadow-2xl"
            style={{ left: `${contextMenu.x + 20}px`, top: `${contextMenu.y + 20}px` }}
            onClick={(event) => event.stopPropagation()}
          >
            <label className="inline-flex items-center gap-1.5 text-[11px] font-semibold uppercase tracking-wide text-slate-500">
              <Tag className="h-3.5 w-3.5" />
              Polygon Name
            </label>
            <input
              value={contextMenu.nameDraft}
              onChange={(event) =>
                setContextMenu((previous) => ({
                  ...previous,
                  nameDraft: event.target.value,
                }))
              }
              className="rounded-md border border-slate-300 px-2 py-1.5 text-sm"
              placeholder="Polygon name"
            />

            <div className="grid grid-cols-3 gap-1.5">
              <button
                onClick={handleSaveContextMenuRename}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-slate-200 px-2 py-2 text-xs font-medium text-slate-800 transition hover:bg-slate-300"
              >
                <PenLine className="h-3.5 w-3.5" />
                Rename
              </button>
              <button
                onClick={() => contextMenu.appFeatureId && void handleSplitFeatureById(contextMenu.appFeatureId)}
                disabled={
                  !contextMenu.appFeatureId ||
                  splittingFeatureIds.has(contextMenu.appFeatureId) ||
                  isSplittingAll
                }
                className="inline-flex items-center justify-center gap-1 rounded-md bg-indigo-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-indigo-500 disabled:cursor-not-allowed disabled:bg-indigo-300"
              >
                {contextMenu.appFeatureId && splittingFeatureIds.has(contextMenu.appFeatureId) ? (
                  <Loader2 className="h-3.5 w-3.5 animate-spin" />
                ) : (
                  <Scissors className="h-3.5 w-3.5" />
                )}
                {contextMenu.appFeatureId && splittingFeatureIds.has(contextMenu.appFeatureId)
                  ? 'Splitting...'
                  : 'Split by State'}
              </button>
              <button
                onClick={() => contextMenu.appFeatureId && handleDeleteFeatureById(contextMenu.appFeatureId)}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-red-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-red-500"
              >
                <Trash2 className="h-3.5 w-3.5" />
                Remove
              </button>
            </div>

            {contextMenu.appFeatureId &&
            polygonItems.find((item) => item.appFeatureId === contextMenu.appFeatureId)?.isMultiPolygon ? (
              <button
                onClick={() => handleSeparatePartsById(contextMenu.appFeatureId as string)}
                className="inline-flex items-center justify-center gap-1 rounded-md bg-sky-600 px-2 py-2 text-xs font-medium text-white transition hover:bg-sky-500"
              >
                <Braces className="h-3.5 w-3.5" />
                Separate Parts
              </button>
            ) : null}
          </div>
        ) : null}
      </main>
    </div>
  );
}
