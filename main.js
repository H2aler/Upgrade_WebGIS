import 'ol/ol.css';
import './styles.css';
import Map from 'ol/Map';
import View from 'ol/View';
import TileLayer from 'ol/layer/Tile';
import VectorLayer from 'ol/layer/Vector';
import VectorSource from 'ol/source/Vector';
import OSM from 'ol/source/OSM';
import XYZ from 'ol/source/XYZ';
import { fromLonLat, toLonLat, transform, transformExtent } from 'ol/proj';
import { defaults as defaultControls, Zoom, ScaleLine } from 'ol/control';
import { Point, LineString, Polygon } from 'ol/geom';
import { Feature } from 'ol';
import { Style, Icon, Stroke, Fill, Circle as CircleStyle, Text } from 'ol/style';
import { Draw, Modify, Snap } from 'ol/interaction';
import { getLength, getArea } from 'ol/sphere';
import { unByKey } from 'ol/Observable';
import Overlay from 'ol/Overlay';
import GeoJSON from 'ol/format/GeoJSON';

// 지도 초기화
class WebGISMap {
    constructor() {
        this.map = null;
        this.vectorSource = new VectorSource();
        this.vectorLayer = new VectorLayer({
            source: this.vectorSource,
            style: (feature) => this.getFeatureStyle(feature)
        });

        this.draw = null;
        this.snap = null;
        this.modify = null;
        this.currentTool = null;
        this.measurementListener = null;
        this.clickListener = null;
        this.measurementFeatures = [];
        this.measurementResults = [];
        this.measurementHistory = [];
        this.searchResults = [];
        this.distanceOverlay = null;
        this.currentDistanceFeature = null;
        // 측정 오버레이들
        this.liveTooltipOverlay = null; // 전체 길이 툴팁
        this.segmentOverlay = null;     // 마지막 구간 배지(수동 모드)
        // 스마트 거리 측정 상태
        this.smartDistanceActive = false;
        this.smartStartCoord = null; // EPSG:3857
        this.smartCoords = [];
        this.smartLineFeature = null;
        this.smartClickKey = null;
        this.smartDblKey = null;
        this.smartSegmentOverlay = null;
        // 이미지 탐색 상태
        this.imageSearchActive = false;
        this.currentImageSearchLocation = null; // 스마트 모드 구간 배지
        // Street View 상태
        this.streetViewActive = false;
        this.mapillaryViewer = null;
        this.streetViewOverlay = null;
        this.isNavigating = false;
        this.streetViewMarker = null;
        this.currentStreetViewLocation = null; // {lat, lon}
        this.mapMoveListener = null; // 지도 이동 이벤트 리스너
        this.lastKnownLocation = null; // {lat, lon}

        // 멀티-스마트 거리 측정 (검색 결과 간 경로)
        this.multiRouteActive = false;
        this.routeCoords = []; // EPSG:3857 좌표 배열
        this.routeLineFeature = null;

        // 검색 결과 마커 관리
        this.searchResultMarkers = [];
        this.searchResultFeatures = [];

        // 즐겨찾기 마커 관리
        this.favoriteMarkers = [];
        this.favoriteFeatures = [];

        // 이미지 위치 추정 관련 상태
        this.imageLocationEstimation = {
            active: false,
            results: []
        };

        // TensorFlow.js 모델 상태
        this.tfModels = {
            cocoSSD: null,
            mobilenet: null,
            loaded: false
        };

        // 외부 AI 라이브러리 로드 상태
        this.aiLibs = {
            exifLoaded: false,
            tesseractLoaded: false,
            tfScriptsLoaded: false
        };

        // 3D 지도 상태 (MapLibre GL)
        this.map3D = null;
        this.is3DActive = false;
        this.map3DMarker = null;
        this.navigationPanel = document.getElementById('navigationPanel');

        this.initMap();
        this.initControls();
        this.initSearch();
        this.initTheme();
        this.initLayerPersistence(); // 레이어 설정 복구
        this.initEventListeners();
        this.renderFavorites();
        this.bindFullscreen();
        this.bindMeasureButtons();

        // 초기 패널 가시성 설정
        this.updatePanelVisibility();

        // 검색창 초기화 (브라우저 캐시 방지)
        const searchInput = document.getElementById('searchInput');
        if (searchInput) {
            searchInput.value = '';
            const clearBtn = document.getElementById('searchClearBtn');
            if (clearBtn) clearBtn.style.display = 'none';
        }
    }

    // 지도 초기화
    initMap() {
        // 기본 OSM 레이어
        const osmLayer = new TileLayer({
            source: new XYZ({
                url: 'https://{a-c}.tile.openstreetmap.org/{z}/{x}/{y}.png',
                attributions: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
                crossOrigin: 'anonymous'
            }),
            title: 'OpenStreetMap'
        });

        // 위성 이미지 레이어 (Google Satellite - 업그레이드됨)
        const satelliteLayer = new TileLayer({
            source: new XYZ({
                url: 'https://mt1.google.com/vt/lyrs=s&x={x}&y={y}&z={z}',
                attributions: '© Google Maps',
                crossOrigin: 'anonymous'
            }),
            title: '위성 이미지',
            visible: false
        });

        // 하이브리드 레이어 (Google Hybrid - 위성 + 라벨)
        const hybridLayer = new TileLayer({
            source: new XYZ({
                url: 'https://mt1.google.com/vt/lyrs=y&x={x}&y={y}&z={z}',
                attributions: '© Google Maps (Hybrid)',
                crossOrigin: 'anonymous'
            }),
            title: '하이브리드',
            visible: false
        });

        // 지형도 레이어 (Google Terrain - 업그레이드됨)
        const terrainLayer = new TileLayer({
            source: new XYZ({
                url: 'https://mt1.google.com/vt/lyrs=p&x={x}&y={y}&z={z}',
                attributions: '© Google Maps (Terrain)',
                crossOrigin: 'anonymous'
            }),
            title: '지형도',
            visible: false
        });

        this.layers = {
            osm: osmLayer,
            satellite: satelliteLayer,
            hybrid: hybridLayer,
            terrain: terrainLayer
        };

        // 초기 지도 모드 확인 (저장된 값이 없으면 OSM 기본)
        const savedLayer = localStorage.getItem('mapLayer') || 'osm';
        if (savedLayer && this.layers[savedLayer]) {
            Object.values(this.layers).forEach(l => l.setVisible(false));
            this.layers[savedLayer].setVisible(true);
        }

        // 지도 생성
        this.map = new Map({
            target: 'map',
            layers: [osmLayer, satelliteLayer, terrainLayer, this.vectorLayer],
            view: new View({
                center: fromLonLat([127.7669, 37.5665]), // 서울 중심
                zoom: 10,
                maxZoom: 19,
                minZoom: 3
            }),
            controls: defaultControls({
                zoom: true,
                attribution: true
            }).extend([
                new ScaleLine({
                    units: 'metric'
                })
            ])
        });

        // 좌표 표시 이벤트
        this.map.on('pointermove', (event) => {
            const coordinate = event.coordinate;
            const lonLat = transform(coordinate, 'EPSG:3857', 'EPSG:4326');
            const coordEl = document.getElementById('coordinates');
            if (coordEl) {
                if (window.innerWidth <= 768) {
                    // 모바일용 아주 컴팩트한 표시
                    coordEl.innerHTML = `LON: ${lonLat[0].toFixed(5)}<br>LAT: ${lonLat[1].toFixed(5)}`;
                } else {
                    coordEl.innerHTML = `경도: ${lonLat[0].toFixed(6)}<br>위도: ${lonLat[1].toFixed(6)}`;
                }
            }
        });

        // 지도 클릭 이벤트 (마커 추가용 및 이미지 탐색용)
        this.map.on('click', (event) => {
            // 네비게이션 지점 선택 모드일 때
            if (this.navSelectionMode) {
                const coordinate = event.coordinate;
                const lonLat = transform(coordinate, 'EPSG:3857', 'EPSG:4326');
                this.setNavPoint(lonLat[1], lonLat[0], this.navSelectionMode);
                this.navSelectionMode = null; // 선택 후 해제
                document.body.style.cursor = 'default';
                return;
            }
            // 이미지 탐색 모드일 때
            if (this.imageSearchActive) {
                const coordinate = event.coordinate;
                this.addImageSearchMarker(coordinate); // 클릭 위치 마커 표시
                const lonLat = transform(coordinate, 'EPSG:3857', 'EPSG:4326');
                this.searchImagesAtLocation(lonLat[1], lonLat[0]);
                return;
            }

            // Street View 모드일 때
            if (this.streetViewActive) {
                const coordinate = event.coordinate;
                const lonLat = transform(coordinate, 'EPSG:3857', 'EPSG:4326');
                this.showStreetView(lonLat[1], lonLat[0]);
                return;
            }

            // 마커 추가 모드일 때
            if (this.currentTool === 'marker') {
                this.addMarker(event.coordinate);
                this.deactivateCurrentTool();
                document.getElementById('addMarker').classList.remove('active');
            }
        });

        // 즐겨찾기 마커 클릭 이벤트 (삭제용)
        this.map.on('click', (event) => {
            const feature = this.map.forEachFeatureAtPixel(event.pixel, (feature) => feature);
            if (feature && feature.get('properties') && feature.get('properties').type === 'favorite') {
                const markerId = feature.get('properties').id;
                if (confirm('이 즐겨찾기 마커를 삭제하시겠습니까?')) {
                    this.removeFavoriteMarker(markerId);
                }
            }
        });
    }

    // 컨트롤 초기화
    initControls() {
        // 줌 인 컨트롤
        document.getElementById('zoomIn').addEventListener('click', () => {
            if (this.is3DActive && this.map3D) {
                this.map3D.zoomTo(this.map3D.getZoom() + 1);
            } else if (this.map) {
                const view = this.map.getView();
                const zoom = view.getZoom();
                view.animate({
                    zoom: zoom + 1,
                    duration: 250
                });
            }
        });

        // 줌 아웃 컨트롤
        document.getElementById('zoomOut').addEventListener('click', () => {
            if (this.is3DActive && this.map3D) {
                this.map3D.zoomTo(this.map3D.getZoom() - 1);
            } else if (this.map) {
                const view = this.map.getView();
                const zoom = view.getZoom();
                view.animate({
                    zoom: zoom - 1,
                    duration: 250
                });
            }
        });

        // 초기 영역으로 이동 (Home)
        document.getElementById('fullExtent').addEventListener('click', () => {
            const seoulLonLat = [127.0276, 37.5045]; // 서울 강남 중심 예시 또는 기본값
            if (this.is3DActive && this.map3D) {
                this.map3D.flyTo({
                    center: seoulLonLat,
                    zoom: 12,
                    pitch: 50,
                    bearing: 0,
                    duration: 1000
                });
            } else if (this.map) {
                const extent4326 = [126.7, 37.3, 127.3, 37.7]; // 서울 근교 범위
                const extent3857 = transformExtent(extent4326, 'EPSG:4326', 'EPSG:3857');
                this.map.getView().fit(extent3857, {
                    padding: [50, 50, 50, 50],
                    duration: 1000
                });
            }
            this.toast('초기 영역으로 이동했습니다.');
        });

        // 레이어 선택
        document.getElementById('layerSelect').addEventListener('change', (event) => {
            this.switchLayer(event.target.value);
            this.toast(`레이어 전환: ${event.target.value}`);
        });
    }

    // 검색 기능 초기화
    initSearch() {
        const searchInput = document.getElementById('searchInput');
        const searchBtn = document.getElementById('searchBtn');
        const searchResults = document.getElementById('searchResults');
        let activeIndex = -1;

        // 검색 버튼 클릭
        searchBtn.addEventListener('click', () => {
            this.performSearch(searchInput.value);
        });

        // 엔터키 검색
        searchInput.addEventListener('keypress', (e) => {
            if (e.key === 'Enter') {
                this.performSearch(searchInput.value);
            }
        });

        // 검색 결과 외부 클릭 시 숨기기
        document.addEventListener('click', (e) => {
            if (!searchInput.contains(e.target) && !searchBtn.contains(e.target) && !searchResults.contains(e.target) && !document.getElementById('searchClearBtn')?.contains(e.target)) {
                this.hideSearchResults();
            }
        });

        // X 버튼 (지우기) 클릭
        const clearBtn = document.getElementById('searchClearBtn');
        if (clearBtn) {
            clearBtn.addEventListener('click', () => {
                searchInput.value = '';
                searchInput.focus();
                clearBtn.style.display = 'none';
                this.hideSearchResults();
            });
        }

        // 입력 시 자동 검색 (디바운싱)
        let searchTimeout;
        searchInput.addEventListener('input', (e) => {
            const val = e.target.value;
            if (clearBtn) {
                clearBtn.style.display = val ? 'block' : 'none';
            }
            clearTimeout(searchTimeout);
            searchTimeout = setTimeout(() => {
                if (val.length >= 2) {
                    this.performSearch(val);
                } else {
                    this.hideSearchResults();
                }
            }, 300);
        });

        // 키보드 탐색
        searchInput.addEventListener('keydown', (e) => {
            const items = Array.from(searchResults.querySelectorAll('.search-result-item'));
            if (!items.length) return;
            if (e.key === 'ArrowDown') {
                e.preventDefault();
                activeIndex = (activeIndex + 1) % items.length;
                this.updateActiveSearchItem(items, activeIndex);
            } else if (e.key === 'ArrowUp') {
                e.preventDefault();
                activeIndex = (activeIndex - 1 + items.length) % items.length;
                this.updateActiveSearchItem(items, activeIndex);
            } else if (e.key === 'Enter') {
                e.preventDefault();
                if (activeIndex >= 0) {
                    items[activeIndex].querySelector('.search-result-content').click();
                } else if (searchBtn) {
                    searchBtn.click();
                }
            } else if (e.key === 'Escape') {
                this.hideSearchResults();
            }
        });
    }

    updateActiveSearchItem(items, index) {
        items.forEach(el => el.classList.remove('active'));
        if (items[index]) {
            items[index].classList.add('active');
            items[index].scrollIntoView({ block: 'nearest' });
        }
    }

    async performSearch(query) {
        if (!query.trim()) {
            this.hideSearchResults();
            return;
        }

        try {
            console.log('🔍 검색 시작:', query);

            // 로딩 상태 표시
            this.showSearchLoading();

            // Nominatim API를 사용한 지오코딩
            const url = `https://nominatim.openstreetmap.org/search?format=json&q=${encodeURIComponent(query)}&limit=5&addressdetails=1&countrycodes=kr,jp,cn,us,gb,fr,de,it,es,ca,au`;
            console.log('📡 API 요청 URL:', url);

            const response = await fetch(url, {
                method: 'GET',
                headers: {
                    'Accept': 'application/json',
                    'User-Agent': 'WebGIS-Application/1.0'
                }
            });

            console.log('📥 응답 상태:', response.status, response.statusText);

            if (!response.ok) {
                throw new Error(`검색 요청 실패: ${response.status} ${response.statusText}`);
            }

            const data = await response.json();
            console.log('✅ 검색 결과:', data);

            this.searchResults = data;
            this.displaySearchResults(data);
        } catch (error) {
            console.error('❌ 검색 오류:', error);
            this.showSearchError(`검색 중 오류가 발생했습니다: ${error.message}`);
        }
    }

    displaySearchResults(results) {
        const searchResults = document.getElementById('searchResults');

        if (!results || results.length === 0) {
            searchResults.innerHTML = '<div class="search-result-item no-results">🔍 검색 결과가 없습니다.</div>';
            searchResults.classList.add('show');
            return;
        }

        console.log('📋 검색 결과 표시:', results.length, '개');

        const headerHTML = `
            <div class="results-header">
                <div class="results-meta">결과 ${results.length}건</div>
                <div class="results-actions">
                    <button id="clearResults">지우기</button>
                </div>
            </div>
        `;

        const resultsHTML = results.map((result, index) => {
            const name = result.display_name.split(',')[0];
            const details = result.display_name.split(',').slice(1, 3).join(',');

            console.log(`📝 검색 결과 ${index} 생성:`, { name, lat: result.lat, lon: result.lon });

            return `
                <div class="search-result-item" data-lat="${result.lat}" data-lon="${result.lon}" data-index="${index}">
                    <div class="search-result-content">
                        <div class="search-result-name">📍 ${name}</div>
                        <div class="search-result-details">${details}</div>
                    </div>
                    <div class="search-result-actions">
                        <button class="favorite-btn" title="즐겨찾기에 추가" data-index="${index}">⭐</button>
                        <button class="smart-measure-btn" title="스마트 거리 측정" data-index="${index}" data-type="distance">📏</button>
                        <button class="smart-measure-btn" title="스마트 면적 측정" data-index="${index}" data-type="area">📐</button>
                    </div>
                </div>
            `;
        }).join('');

        searchResults.innerHTML = headerHTML + resultsHTML;
        searchResults.classList.add('show');

        const clearBtn = document.getElementById('clearResults');
        if (clearBtn) clearBtn.addEventListener('click', () => this.hideSearchResults());

        // 검색 결과 클릭 이벤트 (콘텐츠 영역)
        const contentElements = searchResults.querySelectorAll('.search-result-item .search-result-content');
        console.log('🔗 찾은 검색 결과 콘텐츠 요소 개수:', contentElements.length);

        contentElements.forEach((content, contentIndex) => {
            console.log(`🔗 이벤트 리스너 추가 중 - contentIndex: ${contentIndex}`);
            content.addEventListener('click', (e) => {
                console.log('🔍 검색 결과 클릭됨 - contentIndex:', contentIndex);
                const parent = content.closest('.search-result-item');
                const lat = parseFloat(parent.dataset.lat);
                const lon = parseFloat(parent.dataset.lon);
                const index = parseInt(parent.dataset.index);
                const name = content.querySelector('.search-result-name').textContent.replace('📍 ', '');

                console.log('📍 클릭된 위치:', { lat, lon, name, index });
                console.log('📍 results 배열:', results);
                console.log('📍 results[index]:', results[index]);

                // 위치로 이동
                this.goToLocation(lat, lon);

                // 검색 결과 마커 추가
                this.addSearchResultMarker(lat, lon, name, results[index]);

                // 스마트 거리 측정 시작점으로 설정
                this.startSmartDistanceFrom(lat, lon);

                this.hideSearchResults();
                const searchInput = document.getElementById('searchInput');
                searchInput.value = name;
                const clearBtn = document.getElementById('searchClearBtn');
                if (clearBtn) clearBtn.style.display = 'block';
            });
        });

        // 즐겨찾기 버튼 이벤트
        searchResults.querySelectorAll('.favorite-btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.stopPropagation();
                const index = parseInt(btn.dataset.index);
                this.addToFavorites(results[index]);
            });
        });

        // 스마트 측정 버튼 이벤트
        searchResults.querySelectorAll('.smart-measure-btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.stopPropagation();
                const index = parseInt(btn.dataset.index);
                const type = btn.dataset.type;
                const res = results[index];
                const name = res.display_name.split(',')[0];
                if (type === 'distance') {
                    this.handleMultiSmartDistanceClick(parseFloat(res.lat), parseFloat(res.lon), name);
                } else {
                    this.activateTool('area');
                    document.getElementById('measurementResult').innerHTML = `<div class="measurement-guide">🎯 스마트 면적 측정: "${name}" 기준으로 지도에서 다각형을 그리세요.</div>`;
                }
            });
        });
    }

    // 즐겨찾기 관리
    addToFavorites(result) {
        const name = result.display_name.split(',')[0];
        const item = {
            id: Date.now().toString(),
            name,
            lat: parseFloat(result.lat),
            lon: parseFloat(result.lon),
            addedAt: new Date().toISOString()
        };
        const list = this.getFavorites();
        const exists = list.some(f => f.lat === item.lat && f.lon === item.lon);
        if (exists) return;
        list.push(item);
        localStorage.setItem('favorites', JSON.stringify(list));
        this.renderFavorites();

        // 즐겨찾기 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('favorites-panel', '즐겨찾기에 추가되었습니다!');
    }

    getFavorites() {
        try {
            return JSON.parse(localStorage.getItem('favorites')) || [];
        } catch (_) { return []; }
    }

    removeFavorite(id) {
        const list = this.getFavorites().filter(f => f.id !== id);
        localStorage.setItem('favorites', JSON.stringify(list));
        this.renderFavorites();
    }

    renderFavorites() {
        const container = document.getElementById('favoritesList');
        const list = this.getFavorites();
        if (!container) return;
        if (list.length === 0) {
            container.innerHTML = '<div class="empty">즐겨찾기가 없습니다.</div>';
            return;
        }
        container.innerHTML = list.map(item => `
            <div class="favorite-item">
                <div class="favorite-info">
                    <div class="favorite-icon">📍</div>
                    <div class="favorite-name">${item.name}</div>
                </div>
                <div class="favorite-actions">
                    <button class="go-to-favorite" data-id="${item.id}" data-lat="${item.lat}" data-lon="${item.lon}">이동</button>
                    <button class="remove-favorite" data-id="${item.id}">X</button>
                </div>
            </div>
        `).join('');
        container.querySelectorAll('.go-to-favorite').forEach(btn => {
            btn.addEventListener('click', () => {
                const lat = parseFloat(btn.dataset.lat);
                const lon = parseFloat(btn.dataset.lon);
                this.goToFavoriteLocation(lat, lon);
            });
        });
        container.querySelectorAll('.remove-favorite').forEach(btn => {
            btn.addEventListener('click', () => this.removeFavorite(btn.dataset.id));
        });
        this.updatePanelVisibility();
    }

    // 테마 토글
    initTheme() {
        const btn = document.getElementById('themeToggle');
        const saved = localStorage.getItem('theme') || 'light';
        document.documentElement.dataset.theme = saved;
        if (btn) {
            btn.addEventListener('click', () => {
                const next = (document.documentElement.dataset.theme === 'light') ? 'dark' : 'light';
                document.documentElement.dataset.theme = next;
                localStorage.setItem('theme', next);
            });
        }
    }

    // 스마트 거리 측정: 검색 결과 지점을 시작점으로 설정하고, 사용자가 추가 클릭한 지점까지 누적 거리 계산
    startSmartDistanceFrom(lat, lon) {
        // 시작점 표시 및 지도 이동
        const start3857 = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
        this.goToLocation(lat, lon);

        // 상태 초기화
        this.smartDistanceActive = true;
        this.smartStartCoord = start3857;
        this.smartCoords = [start3857];

        // 기존 라인 제거
        if (this.smartLineFeature) {
            this.vectorSource.removeFeature(this.smartLineFeature);
            this.smartLineFeature = null;
        }

        // 안내 메시지
        document.getElementById('measurementResult').innerHTML =
            '<div class="measurement-guide">시작점이 설정되었습니다. 지도를 클릭해 지점을 추가하세요. 더블클릭으로 측정을 완료합니다.</div>';

        // 측정 결과 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('measurement-panel', '스마트 거리 측정을 시작합니다!');

        // 지도 클릭으로 지점 추가
        if (this.smartClickKey) this.map.un('click', this.smartClickKey);
        this.smartClickKey = this.map.on('click', (evt) => {
            if (!this.smartDistanceActive) return;
            const coord = evt.coordinate;
            this.smartCoords.push(coord);
            this.updateSmartDistanceLine();
        });

        // 더블클릭으로 완료
        if (this.smartDblKey) this.map.un('dblclick', this.smartDblKey);
        this.smartDblKey = this.map.on('dblclick', (evt) => {
            if (!this.smartDistanceActive) return;
            evt.preventDefault?.();
            this.finishSmartDistance();
        });
    }

    // 멀티-스마트: 검색 결과 지점 간 경로 누적
    handleMultiSmartDistanceClick(lat, lon, name) {
        const coord3857 = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
        // 경로 시작이 아니면 중간/마지막 선택
        if (!this.multiRouteActive) {
            this.multiRouteActive = true;
            this.routeCoords = [coord3857];
            this.toast(`시작점: ${name}`);
            document.getElementById('measurementResult').innerHTML = '<div class="measurement-guide">다음 검색 결과의 📏을 눌러 중간 또는 마지막 구간을 선택하세요.</div>';

            // 측정 결과 패널로 스크롤 및 하이라이트
            this.highlightAndScrollToPanel('measurement-panel', '멀티 경로 측정을 시작합니다!');
            return;
        }

        // 지도 위 선택 패널 표시
        const panel = document.getElementById('routeChoice');
        const nameEl = document.getElementById('routeChoiceName');
        const addMid = document.getElementById('routeAddMid');
        const addLast = document.getElementById('routeAddLast');
        const cancelBtn = document.getElementById('routeCancelChoice');
        nameEl.textContent = name;
        panel.style.display = 'block';
        // 검색창 우측으로 위치 이동
        const searchEl = document.querySelector('.search-container');
        if (searchEl) {
            const rect = searchEl.getBoundingClientRect();
            panel.style.top = `${rect.top + rect.height + 8}px`;
            panel.style.left = `${rect.right + 8}px`;
        }

        const onChooseMid = () => {
            panel.style.display = 'none';
            addMid.removeEventListener('click', onChooseMid);
            addLast.removeEventListener('click', onChooseLast);
            cancelBtn.removeEventListener('click', onCancel);
            this.routeCoords.push(coord3857);
            this.updateRoutePreview();
            this.toast(`중간 구간 추가: ${name}`);
        };
        const onChooseLast = () => {
            panel.style.display = 'none';
            addMid.removeEventListener('click', onChooseMid);
            addLast.removeEventListener('click', onChooseLast);
            cancelBtn.removeEventListener('click', onCancel);
            this.routeCoords.push(coord3857);
            this.updateRoutePreview();
            this.finishMultiRoute();
        };
        const onCancel = () => {
            panel.style.display = 'none';
            addMid.removeEventListener('click', onChooseMid);
            addLast.removeEventListener('click', onChooseLast);
            cancelBtn.removeEventListener('click', onCancel);
        };
        addMid.addEventListener('click', onChooseMid);
        addLast.addEventListener('click', onChooseLast);
        cancelBtn.addEventListener('click', onCancel);
    }

    updateRoutePreview() {
        const line = new LineString(this.routeCoords);
        if (!this.routeLineFeature) {
            this.routeLineFeature = new Feature({ geometry: line });
            this.routeLineFeature.setStyle(new Style({ stroke: new Stroke({ color: '#1e90ff', width: 3 }) }));
            this.vectorSource.addFeature(this.routeLineFeature);
        } else {
            this.routeLineFeature.setGeometry(line);
        }
    }

    finishMultiRoute() {
        if (this.routeCoords.length < 2) { this.resetMultiRoute(); return; }
        // 구간 합산
        let total = 0;
        const segments = [];
        for (let i = 1; i < this.routeCoords.length; i++) {
            const seg = new LineString([this.routeCoords[i - 1], this.routeCoords[i]]);
            const len = getLength(seg);
            total += len;
            segments.push(this.formatDistance(len));
        }
        const resultText = this.formatDistance(total);
        this.measurementResults.push({ type: 'distance', value: total, text: `경로 합계: ${resultText}`, coordinates: this.routeCoords });
        this.updateMeasurementDisplay();
        document.getElementById('measurementResult').innerHTML = `<div class="measurement-success">✅ 경로 합계: ${resultText}<br/><small>${segments.join(' • ')}</small></div>`;
        this.toast('멀티-스마트 거리 측정 완료');
        this.resetMultiRoute();
    }

    resetMultiRoute() {
        this.multiRouteActive = false;
        this.routeCoords = [];
        if (this.routeLineFeature) { this.vectorSource.removeFeature(this.routeLineFeature); this.routeLineFeature = null; }
    }

    updateSmartDistanceLine() {
        // 라인 생성/업데이트
        const line = new LineString(this.smartCoords);
        if (!this.smartLineFeature) {
            this.smartLineFeature = new Feature({ geometry: line });
            this.smartLineFeature.set('type', 'measurement');
            this.smartLineFeature.set('measurement', 'distance');
            this.smartLineFeature.setStyle(new Style({
                stroke: new Stroke({ color: '#28a745', width: 3, lineDash: [5, 5] })
            }));
            this.vectorSource.addFeature(this.smartLineFeature);
        } else {
            this.smartLineFeature.setGeometry(line);
        }

        const len = getLength(line);
        if (!this.liveTooltipOverlay) {
            const el = document.createElement('div');
            el.className = 'toast';
            el.style.pointerEvents = 'none';
            this.liveTooltipOverlay = new Overlay({ element: el, offset: [10, -10], positioning: 'bottom-left' });
            this.map.addOverlay(this.liveTooltipOverlay);
        }
        this.liveTooltipOverlay.getElement().textContent = this.formatDistance(len);
        this.liveTooltipOverlay.setPosition(this.smartCoords[this.smartCoords.length - 1]);

        // 스마트 모드 구간 배지
        if (this.smartCoords.length >= 2) {
            const a = this.smartCoords[this.smartCoords.length - 2];
            const b = this.smartCoords[this.smartCoords.length - 1];
            const mid = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
            const segLen = getLength(new LineString([a, b]));
            if (!this.smartSegmentOverlay) {
                const el = document.createElement('div');
                el.className = 'toast';
                el.style.pointerEvents = 'none';
                this.smartSegmentOverlay = new Overlay({ element: el, offset: [0, -10], positioning: 'bottom-center' });
                this.map.addOverlay(this.smartSegmentOverlay);
            }
            this.smartSegmentOverlay.getElement().textContent = this.formatDistance(segLen);
            this.smartSegmentOverlay.setPosition(mid);
        }
    }

    finishSmartDistance() {
        if (!this.smartDistanceActive || this.smartCoords.length < 2) return;
        const line = new LineString(this.smartCoords);
        const length = getLength(line);
        const resultText = this.formatDistance(length);
        this.measurementResults.push({ type: 'distance', value: length, text: resultText, coordinates: this.smartCoords });
        this.measurementHistory.unshift({ type: 'distance', value: length, text: resultText, when: new Date().toISOString() });
        document.getElementById('measurementResult').innerHTML = `<div class="measurement-success">✅ ${resultText} 측정 완료!</div>`;
        this.updateMeasurementDisplay();
        this.renderMeasureHistory();

        // 상태 정리
        this.smartDistanceActive = false;
        if (this.liveTooltipOverlay) { this.map.removeOverlay(this.liveTooltipOverlay); this.liveTooltipOverlay = null; }
        if (this.smartSegmentOverlay) { this.map.removeOverlay(this.smartSegmentOverlay); this.smartSegmentOverlay = null; }
        if (this.smartClickKey) { this.map.un('click', this.smartClickKey); this.smartClickKey = null; }
        if (this.smartDblKey) { this.map.un('dblclick', this.smartDblKey); this.smartDblKey = null; }
    }

    hideSearchResults() {
        const searchResults = document.getElementById('searchResults');
        searchResults.classList.remove('show');
    }

    showSearchLoading() {
        const searchResults = document.getElementById('searchResults');
        searchResults.innerHTML = '<div class="search-result-item loading">🔍 검색 중...</div>';
        searchResults.classList.add('show');
    }

    showSearchError(message) {
        const searchResults = document.getElementById('searchResults');
        searchResults.innerHTML = `<div class="search-result-item error">❌ ${message}</div>`;
        searchResults.classList.add('show');
    }

    goToLocation(lat, lon) {
        console.log('🗺️ 위치로 이동:', lat, lon);

        // 3D View 모드일 경우
        if (this.is3DActive && this.map3D) {
            console.log('🧱 3D View 이동');

            this.map3D.flyTo({
                center: [lon, lat],
                zoom: 15,
                pitch: 50,
                essential: true
            });

            // 3D 마커 추가
            if (this.map3DMarker) {
                this.map3DMarker.remove();
            }
            if (window.maplibregl) {
                const el = document.createElement('div');
                el.className = 'map3d-marker';
                this.map3DMarker = new maplibregl.Marker(el)
                    .setLngLat([lon, lat])
                    .addTo(this.map3D);
            }

            this.toast(`📍 ${lat.toFixed(4)}, ${lon.toFixed(4)} 로 이동 (3D View)`);

            // 2D 지도도 백그라운드에서 이동시켜 둠 (동기화)
            if (this.map) {
                const coordinates = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
                this.map.getView().animate({ center: coordinates, zoom: 12, duration: 1000 });
            }
            return;
        }

        if (!this.map) {
            console.error('❌ 지도 객체가 없습니다!');
            return;
        }

        const coordinates = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
        console.log('📍 변환된 좌표:', coordinates);

        try {
            this.map.getView().animate({
                center: coordinates,
                zoom: 12,
                duration: 1000
            });
            console.log('✅ 지도 애니메이션 시작됨');
            this.toast(`📍 ${lat.toFixed(4)}, ${lon.toFixed(4)} 로 이동`);

            // 마커 추가
            this.addSearchMarker(lat, lon);

            // 성공 메시지 표시
            setTimeout(() => {
                document.getElementById('measurementResult').innerHTML =
                    `<div class="measurement-success">✅ 위치로 이동했습니다! (${lat.toFixed(4)}, ${lon.toFixed(4)})</div>`;
            }, 500);
        } catch (error) {
            console.error('❌ 지도 이동 중 오류:', error);
        }
    }

    // 즐겨찾기 위치로 이동 (주황색 마커)
    goToFavoriteLocation(lat, lon) {
        console.log('⭐ 즐겨찾기 위치로 이동:', lat, lon);

        if (!this.map) {
            console.error('❌ 지도 객체가 없습니다!');
            return;
        }

        const coordinates = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
        console.log('📍 변환된 좌표:', coordinates);

        try {
            this.map.getView().animate({
                center: coordinates,
                zoom: 12,
                duration: 1000
            });
            console.log('✅ 지도 애니메이션 시작됨');
            this.toast(`⭐ 즐겨찾기 위치로 이동 (${lat.toFixed(4)}, ${lon.toFixed(4)})`);

            // 즐겨찾기 마커 추가 (영구적)
            this.addFavoriteMarker(lat, lon);

            // 성공 메시지 표시
            setTimeout(() => {
                document.getElementById('measurementResult').innerHTML =
                    `<div class="measurement-success">⭐ 즐겨찾기 위치로 이동했습니다! (${lat.toFixed(4)}, ${lon.toFixed(4)})</div>`;
            }, 500);
        } catch (error) {
            console.error('❌ 지도 이동 중 오류:', error);
        }
    }

    // 전체 화면 토글
    bindFullscreen() {
        const btn = document.getElementById('fullscreenToggle');
        if (!btn) return;
        btn.addEventListener('click', () => {
            const docEl = document.documentElement;
            if (!document.fullscreenElement) {
                docEl.requestFullscreen?.();
            } else {
                document.exitFullscreen?.();
            }
        });
    }

    // 토스트 메시지
    toast(message) {
        if (this.isNavigating) return; // 네비게이션 중에는 토스트 억제
        const container = document.getElementById('toastContainer');
        if (!container) return;
        const el = document.createElement('div');
        el.className = 'toast';
        el.textContent = message;
        container.appendChild(el);
        setTimeout(() => {
            el.remove();
        }, 2000);
    }

    // 토스트 메시지 (타입별)
    showToast(message, type = 'info') {
        if (this.isNavigating && type !== 'error') return; // 네비게이션 중에는 중요한 에러 외 억제
        const container = document.getElementById('toastContainer');
        if (!container) return;
        const el = document.createElement('div');
        el.className = `toast toast-${type}`;
        el.textContent = message;
        container.appendChild(el);
        setTimeout(() => {
            el.remove();
        }, 3000);
    }

    // 패널 하이라이트 및 스크롤
    highlightAndScrollToPanel(panelClass, message = '') {
        const panel = document.querySelector(`.${panelClass}`);
        const sidebar = document.querySelector('.sidebar');
        if (!panel) {
            console.warn(`패널을 찾을 수 없습니다: ${panelClass}`);
            return;
        }

        // 모바일인 경우 사이드바 내부 스크롤 처리
        if (window.innerWidth <= 768 && sidebar) {
            const panelTop = panel.offsetTop;
            const sidebarScrollTop = sidebar.scrollTop;
            const sidebarHeight = sidebar.offsetHeight;

            // 패널이 화면 밖이나 너무 아래에 있다면 위로 스크롤
            sidebar.scrollTo({
                top: panelTop - 60, // 핸들 공간 고려
                behavior: 'smooth'
            });
        } else {
            // 데스크탑 또는 일반적인 경우
            panel.scrollIntoView({
                behavior: 'smooth',
                block: 'center'
            });
        }

        // 하이라이트 효과 추가
        panel.classList.add('panel-highlight');

        // 메시지가 있으면 토스트로 표시
        if (message) {
            setTimeout(() => {
                this.showToast(message, 'info');
            }, 500);
        }

        // 3초 후 하이라이트 제거
        setTimeout(() => {
            panel.classList.remove('panel-highlight');
        }, 3000);
    }

    addSearchMarker(lat, lon, isFavorite = false) {
        const coordinates = transform([lon, lat], 'EPSG:4326', 'EPSG:3857');
        const point = new Point(coordinates);

        const feature = new Feature({
            geometry: point,
            type: 'marker',
            search: true,
            isFavorite: isFavorite
        });

        // 즐겨찾기 마커인지에 따라 다른 스타일 적용
        if (isFavorite) {
            feature.setStyle(this.getFavoriteMarkerStyle());
        }

        this.vectorSource.addFeature(feature);

        // 즐겨찾기 마커가 아닌 경우에만 3초 후 자동 제거
        if (!isFavorite) {
            setTimeout(() => {
                this.vectorSource.removeFeature(feature);
            }, 3000);
        }
    }

    // 즐겨찾기 마커 추가 (영구적)
    addFavoriteMarker(lat, lon) {
        console.log('⭐ 즐겨찾기 마커 추가:', { lat, lon });

        const coord = fromLonLat([lon, lat]);
        console.log('📍 변환된 좌표:', coord);

        // 기존 마커가 있는지 확인
        const existingMarker = this.favoriteMarkers.find(marker =>
            marker.lat === lat && marker.lon === lon
        );

        if (existingMarker) {
            console.log('⚠️ 이미 존재하는 즐겨찾기 마커:', existingMarker);
            // 이미 존재하는 마커라면 해당 위치로 이동만
            this.goToLocation(lat, lon);
            return;
        }

        // 새로운 즐겨찾기 마커 생성
        const marker = {
            id: Date.now().toString(),
            lat: lat,
            lon: lon,
            coord: coord,
            addedAt: new Date().toISOString(),
            type: 'favorite'
        };

        console.log('🆕 새 즐겨찾기 마커 객체 생성:', marker);

        // 마커 피처 생성
        const feature = new Feature({
            geometry: new Point(coord),
            properties: marker
        });

        // 즐겨찾기 마커 전용 스타일 적용
        feature.setStyle(this.getFavoriteMarkerStyle());

        // 벡터 레이어에 추가
        this.vectorSource.addFeature(feature);
        console.log('✅ 벡터 레이어에 즐겨찾기 피처 추가됨');

        // 마커 정보 저장
        this.favoriteMarkers.push(marker);
        this.favoriteFeatures.push(feature);
        console.log('💾 즐겨찾기 마커 정보 저장됨. 총 개수:', this.favoriteMarkers.length);

        // 토스트 메시지 표시
        this.showToast(`⭐ 즐겨찾기 마커가 추가되었습니다.`, 'success');

        console.log('✅ 즐겨찾기 마커 추가 완료:', marker);
    }

    // 이벤트 리스너 초기화
    initEventListeners() {
        // 레이어 선택 이벤트
        document.getElementById('layerSelect').addEventListener('change', (e) => {
            this.switchLayer(e.target.value);
        });

        // 도구 버튼 이벤트
        document.getElementById('navTool').addEventListener('click', () => {
            this.toggleNavPanel();
        });

        // 헤더 네비게이션 버튼 (검색창 왼쪽)
        document.getElementById('navToolHeader').addEventListener('click', () => {
            this.toggleNavPanel();
        });

        // 모바일: 사이드바 토글 기능 제거 (수동 리사이즈와 충돌 방지)
        // 기존의 .expanded 토글 코드를 삭제하고 리사이즈 핸들이 모든 제어를 담당하게 함


        // 내 위치 사용 버튼
        const useMyLocationBtn = document.getElementById('useMyLocation');
        if (useMyLocationBtn) {
            useMyLocationBtn.addEventListener('click', () => {
                this.handleUseMyLocation();
            });
        }

        // 실시간 추적 토글
        const trackLocationToggle = document.getElementById('trackLocation');
        if (trackLocationToggle) {
            trackLocationToggle.addEventListener('change', (e) => {
                this.toggleTracking(e.target.checked);
            });
        }

        // 네비게이션 시작 버튼
        const startNavBtn = document.getElementById('startNavBtn');
        if (startNavBtn) {
            startNavBtn.addEventListener('click', () => {
                this.startNavigation();
            });
        }

        // 내 위치로 버튼 (리센터)
        const recenterBtn = document.getElementById('recenterBtn');
        if (recenterBtn) {
            recenterBtn.addEventListener('click', () => {
                this.recenterToCurrentLocation();
            });
        }

        document.getElementById('measureDistance').addEventListener('click', () => {
            this.activateTool('distance');
        });

        document.getElementById('measureArea').addEventListener('click', () => {
            this.activateTool('area');
        });

        document.getElementById('addMarker').addEventListener('click', () => {
            this.activateTool('marker');
        });

        document.getElementById('clearAll').addEventListener('click', () => {
            this.clearAllFeatures();
        });

        document.getElementById('exportData').addEventListener('click', () => {
            this.exportData();
        });

        // Street View 닫기 버튼
        const closeStreetViewBtn = document.getElementById('closeStreetView');
        if (closeStreetViewBtn) {
            closeStreetViewBtn.addEventListener('click', () => {
                this.deactivateStreetViewMode();
                // 레이어를 OSM으로 전환
                const layerSelect = document.getElementById('layerSelect');
                if (layerSelect) {
                    layerSelect.value = 'osm';
                    this.switchLayer('osm');
                }
            });
        }

        // 이미지 업로드 이벤트
        const imageUpload = document.getElementById('imageUpload');
        if (imageUpload) {
            imageUpload.addEventListener('change', (e) => {
                this.handleImageUpload(e);
            });
        }

        // 이미지 탐색 버튼 이벤트
        const imageSearchBtn = document.getElementById('imageSearchBtn');
        if (imageSearchBtn) {
            imageSearchBtn.addEventListener('click', () => {
                this.toggleImageSearch();
            });
        }

        // 로그인 관련 이벤트
        const loginBtn = document.getElementById('loginBtn');
        const loginPassword = document.getElementById('loginPassword');
        if (loginBtn && loginPassword) {
            loginBtn.addEventListener('click', () => this.handleLogin());
            loginPassword.addEventListener('keypress', (e) => {
                if (e.key === 'Enter') this.handleLogin();
            });
        }

        // 로그아웃(시스템 잠금) 관련 이벤트
        const logoutBtn = document.getElementById('logoutBtn');
        if (logoutBtn) {
            logoutBtn.addEventListener('click', () => {
                const confirmed = confirm('시스템을 잠그고 초기화 후 새로 고침하시겠습니까?');
                if (confirmed) {
                    // 지도 레이어 등 저장된 설정 초기화
                    localStorage.removeItem('mapLayer');
                    // 페이지 새로 고침 (비밀번호 입력창이 나타나며 모든 상태 초기화됨)
                    window.location.reload();
                }
            });
        }

    }

    // 로그인 처리
    // 로그인 처리
    async handleLogin() {
        const passwordInput = document.getElementById('loginPassword');
        const errorMsg = document.getElementById('loginError');
        const overlay = document.getElementById('loginOverlay');
        const mainContainer = document.getElementById('mainContainer');

        // 비밀번호 해시값 (보안을 위해 평문 대신 SHA-256 해시 사용)
        // 원문: H2aler_useOwn_webGIS
        const targetHash = 'f1f024673f749031d23dae55cfc8cb4eb7ab0c70cee3280b330e7da593f29528';

        try {
            const inputHash = await this.hashPassword(passwordInput.value);

            if (inputHash === targetHash) {
                // 성공: 오버레이 제거 및 메인 콘텐츠 표시
                if (overlay) overlay.classList.add('hidden');
                if (mainContainer) {
                    mainContainer.style.filter = 'none';
                    mainContainer.style.pointerEvents = 'auto';
                    mainContainer.style.opacity = '1';
                }
                this.toast('반갑습니다! 시스템에 접속되었습니다. 🌍');

                // 0.8초 후 오버레이를 DOM에서 완전히 숨김
                setTimeout(() => {
                    if (overlay) overlay.style.display = 'none';
                }, 800);
            } else {
                // 실패: 에러 메시지 표시 및 입력창 초기화
                if (errorMsg) {
                    errorMsg.style.display = 'block';
                    errorMsg.style.animation = 'none';
                    void errorMsg.offsetWidth;
                    errorMsg.style.animation = null;
                }
                passwordInput.value = '';
                passwordInput.focus();
            }
        } catch (error) {
            console.error('Login error:', error);
            this.toast('로그인 처리 중 오류가 발생했습니다.');
        }
    }

    // SHA-256 해시 생성 함수
    async hashPassword(password) {
        const encoder = new TextEncoder();
        const data = encoder.encode(password);
        const hashBuffer = await crypto.subtle.digest('SHA-256', data);
        const hashArray = Array.from(new Uint8Array(hashBuffer));
        const hashHex = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
        return hashHex;
    }

    // 측정 패널 버튼 바인딩
    bindMeasureButtons() {
        const finishBtn = document.getElementById('finishMeasure');
        const cancelBtn = document.getElementById('cancelMeasure');
        const resetBtn = document.getElementById('resetMeasure');
        if (finishBtn) finishBtn.addEventListener('click', () => this.finishAnyMeasurement());
        if (cancelBtn) cancelBtn.addEventListener('click', () => this.cancelAnyMeasurement());
        if (resetBtn) resetBtn.addEventListener('click', () => this.resetCurrentMeasurement());
    }

    finishAnyMeasurement() {
        // 우선순위: Draw → 스마트 → 멀티 경로
        if (this.draw) {
            this.draw.finishDrawing?.();
            return;
        }
        if (this.smartDistanceActive) {
            this.finishSmartDistance();
            return;
        }
        if (this.multiRouteActive) {
            this.finishMultiRoute();
            return;
        }
        this.toast('진행 중인 측정이 없습니다.');
    }

    cancelAnyMeasurement() {
        // Draw 측정 취소 및 정리
        if (this.draw) {
            this.deactivateCurrentTool();
        }
        // 스마트 측정 정리
        if (this.smartDistanceActive) {
            this.smartDistanceActive = false;
            this.smartCoords = [];
            this.smartStartCoord = null;
            if (this.smartLineFeature) { this.vectorSource.removeFeature(this.smartLineFeature); this.smartLineFeature = null; }
        }
        // 멀티 경로 정리
        if (this.multiRouteActive) {
            this.resetMultiRoute();
        }
        // 오버레이/선택패널 정리
        if (this.liveTooltipOverlay) { this.map.removeOverlay(this.liveTooltipOverlay); this.liveTooltipOverlay = null; }
        if (this.segmentOverlay) { this.map.removeOverlay(this.segmentOverlay); this.segmentOverlay = null; }
        if (this.smartSegmentOverlay) { this.map.removeOverlay(this.smartSegmentOverlay); this.smartSegmentOverlay = null; }
        const panel = document.getElementById('routeChoice');
        if (panel) panel.style.display = 'none';
        this.toast('측정을 취소했습니다.');
    }

    resetCurrentMeasurement() {
        // 스마트 측정: 시작점만 남기고 초기화
        if (this.smartDistanceActive && this.smartStartCoord) {
            this.smartCoords = [this.smartStartCoord];
            if (this.smartLineFeature) {
                this.smartLineFeature.setGeometry(new LineString(this.smartCoords));
            } else {
                this.updateSmartDistanceLine();
            }
            this.toast('스마트 거리 측정을 시작점으로 초기화했습니다.');
            return;
        }
        // 멀티 경로: 첫 지점만 남기고 초기화
        if (this.multiRouteActive && this.routeCoords.length > 0) {
            this.routeCoords = [this.routeCoords[0]];
            this.updateRoutePreview();
            this.toast('경로를 시작점으로 초기화했습니다.');
            return;
        }
        this.toast('초기화할 진행 중 측정이 없습니다.');
    }

    // 레이어 전환
    switchLayer(layerType) {
        // Street View, 3D View는 별도 모드로 처리 (타일 레이어가 아님)
        if (layerType === 'streetview') {
            this.deactivate3DView();
            this.activateStreetViewMode();
            return;
        }
        if (layerType === '3d') {
            this.deactivateStreetViewMode();
            this.activate3DView();
            return;
        }

        this.deactivate3DView();
        Object.values(this.layers).forEach(layer => {
            layer.setVisible(false);
        });

        if (this.layers[layerType]) {
            this.layers[layerType].setVisible(true);
            this.deactivateStreetViewMode();
        }

        // 레이어 선택 상태 저장
        localStorage.setItem('mapLayer', layerType);
    }

    // 레이어 설정 복구
    initLayerPersistence() {
        const savedLayer = localStorage.getItem('mapLayer');
        const layerSelect = document.getElementById('layerSelect');

        if (savedLayer && layerSelect) {
            // UI 업데이트
            layerSelect.value = savedLayer;
            // 지도 업데이트
            this.switchLayer(savedLayer);
            console.log(`📡 이전 레이어 설정 복구: ${savedLayer}`);
        }
    }

    // Street View 모드 활성화
    activateStreetViewMode() {
        this.streetViewActive = true;
        const panel = document.getElementById('streetViewPanel');
        if (panel) {
            panel.style.display = 'block';
            setTimeout(() => {
                panel.scrollIntoView({
                    behavior: 'smooth',
                    block: 'start',
                    inline: 'nearest'
                });
            }, 100);
        }
        this.showToast('🛣️ Street View 모드가 활성화되었습니다. 지도를 클릭하세요.', 'info');
    }

    // Street View 모드 비활성화
    deactivateStreetViewMode() {
        this.streetViewActive = false;
        const panel = document.getElementById('streetViewPanel');
        if (panel) {
            panel.style.display = 'none';
        }
        // 기존 Mapillary 관련 코드는 더 이상 사용하지 않음
    }

    // 3D View 활성화 (MapLibre GL)
    activate3DView(targetLat = null, targetLon = null) {
        this.is3DActive = true;
        const map3dEl = document.getElementById('map3d');
        if (!map3dEl) return;

        // OpenLayers 지도를 숨기고 3D 컨테이너를 표시
        const mapEl = document.getElementById('map');
        if (mapEl) {
            mapEl.style.visibility = 'hidden';
        }
        map3dEl.style.display = 'block';

        // 현재 OL 뷰 또는 전달받은 좌표 기준으로 중심/줌 계산
        const view = this.map.getView();
        let center = view.getCenter();
        let lonLat = center ? toLonLat(center) : [127.7669, 37.5665];
        if (targetLat !== null && targetLon !== null) {
            lonLat = [targetLon, targetLat];
        }
        const zoom = view.getZoom() || 10;

        if (!this.map3D && window.maplibregl) {
            // 2.5D 네비게이션을 위한 최적화된 설정
            // 기본 MapLibre 스타일 사용 (안정적이고 무료)
            this.map3D = new maplibregl.Map({
                container: 'map3d',
                style: 'https://tiles.openfreemap.org/styles/liberty',
                center: lonLat,
                zoom: Math.max(zoom, 13), // 최소 줌 레벨 13으로 설정
                pitch: 50, // 2.5D 네비게이션에 적합한 각도
                bearing: 0,
                antialias: true
            });

            // 지형 높이 데이터 및 2.5D 효과 추가
            this.map3D.on('load', () => {
                try {
                    // 1. 하늘 배경 추가 (고급스러운 분위기 연출)
                    this.map3D.setSky({
                        'sky-type': 'gradient',
                        'sky-atmosphere-sun': [0.0, 0.0],
                        'sky-atmosphere-sun-intensity': 15
                    });

                    // 4. 안개 효과 추가 (지평선 경계를 부드럽게 처리)
                    this.map3D.setFog({
                        'range': [1, 10],
                        'color': '#ffffff',
                        'horizon-blend': 0.1
                    });

                    // 5. 3D 건물 레이어 추가 (OpenFreeMap 벡터 타일 사용)
                    // openfreemap 스타일은 'openmaptiles'라는 소스 이름을 사용함
                    const layers = this.map3D.getStyle().layers;
                    let labelLayerId;
                    for (let i = 0; i < layers.length; i++) {
                        if (layers[i].type === 'symbol' && layers[i].layout['text-field']) {
                            labelLayerId = layers[i].id;
                            break;
                        }
                    }

                    this.map3D.addLayer({
                        'id': '3d-buildings',
                        'source': 'openmaptiles',
                        'source-layer': 'building',
                        'filter': ['==', 'extrude', 'true'],
                        'type': 'fill-extrusion',
                        'minzoom': 13,
                        'paint': {
                            'fill-extrusion-color': [
                                'coalesce',
                                ['get', 'colour'], // 건물 개별 색상 정보 우선
                                [
                                    'case',
                                    // 용도별 현실적인 색상 매핑
                                    ['match', ['get', 'class'],
                                        ['residential', 'apartments', 'house'], true, false
                                    ], '#fdfcf0', // 주거용 (따뜻한 베이지/황토색 계열)
                                    ['match', ['get', 'class'],
                                        ['commercial', 'retail', 'mall'], true, false
                                    ], '#eef5f9', // 상업용 (현대적인 블루글라스/실버 톤)
                                    ['match', ['get', 'class'],
                                        ['school', 'university', 'hospital', 'public'], true, false
                                    ], '#f9f3e9', // 공공기관/학교 (안정적인 오프화이트)
                                    ['==', ['get', 'class'], 'industrial'], '#f4f4f4', // 산업용 (무채색 콘크리트)
                                    // 기본값: 높이에 따른 컬러 그라데이션 (더 역동적인 색감)
                                    [
                                        'interpolate',
                                        ['linear'],
                                        ['get', 'render_height'],
                                        0, '#f9f7f2',      // 낮은 건물
                                        20, '#e5e1d8',     // 중간 빌딩
                                        50, '#9eb2c0',     // 중고층 (유리 느낌)
                                        100, '#3a5a78',    // 고층 (짙은 네이비/글라스)
                                        200, '#2c3e50'     // 초고층 (웅장한 다크톤)
                                    ]
                                ]
                            ],
                            'fill-extrusion-height': [
                                'interpolate', ['linear'], ['zoom'],
                                13, 0,
                                13.05, ['get', 'render_height']
                            ],
                            'fill-extrusion-base': [
                                'interpolate', ['linear'], ['zoom'],
                                13, 0,
                                13.05, ['get', 'render_min_height']
                            ],
                            'fill-extrusion-opacity': 0.95, // 조금 더 견고한 느낌
                            'fill-extrusion-vertical-gradient': true
                        }
                    }, labelLayerId);

                    // 6. 실제 같은 조명 효과 설정 (입체감 강화)
                    this.map3D.setLight({
                        anchor: 'viewport',
                        color: 'white',
                        intensity: 0.5,
                        position: [1.5, 135, 45] // 그림자가 더 선명하게 드리워지는 각도
                    });

                } catch (e) {
                    console.warn('3D 레이어 추가 중 오류:', e);
                }
            });

            // 3D 모드 클릭 통합 이벤트 (이동, 클릭 상호작용 모두 지원)
            this.map3D.on('click', async (e) => {
                const lonLat = [e.lngLat.lng, e.lngLat.lat];

                // 1~4. 기존 모드 처리 (네비게이션, 이미지 탐색 등)
                if (this.navSelectionMode || this.imageSearchActive || this.streetViewActive || this.currentTool === 'marker') {
                    // 기존 로직 유지 (생략된 부분은 실제 코드에서 유지됨)
                    if (this.navSelectionMode) {
                        this.setNavPoint(e.lngLat.lat, e.lngLat.lng, this.navSelectionMode);
                        this.navSelectionMode = null;
                        document.body.style.cursor = 'default';
                        return;
                    }
                    if (this.imageSearchActive) {
                        this.addImageSearchMarker(transform(lonLat, 'EPSG:4326', 'EPSG:3857'));
                        this.searchImagesAtLocation(e.lngLat.lat, e.lngLat.lng);
                        return;
                    }
                    if (this.streetViewActive) {
                        this.showStreetView(e.lngLat.lat, e.lngLat.lng);
                        return;
                    }
                    if (this.currentTool === 'marker') {
                        this.addMarker(transform(lonLat, 'EPSG:4326', 'EPSG:3857'));
                        this.deactivateCurrentTool();
                        const markerBtn = document.getElementById('addMarker');
                        if (markerBtn) markerBtn.classList.remove('active');
                        return;
                    }
                }

                // 5. POI(가게, 역 등) 정보 팝업 표시
                const features = this.map3D.queryRenderedFeatures(e.point);
                if (!features || features.length === 0) return;

                // 우선순위 결정: 클릭한 지점의 레이어 순서를 고려하되, 이름이 있는 POI를 최우선
                // 1. POI 레이어 (아이콘/라벨)
                // 2. 교통 요지/장소명
                // 3. 3D 건물 (footprint)
                const poiFeature = features.find(f => (f.layer.id.includes('poi') || f.layer.id.includes('place')) && (f.properties.name || f.properties.name_en));
                const buildingFeature = features.find(f => f.layer.id === '3d-buildings');

                // 사용자가 아이콘을 정확히 클릭했는지, 아니면 빈 공간(건물)을 클릭했는지 판단
                const feature = poiFeature || buildingFeature;
                if (!feature) return;

                const props = feature.properties;
                const tileName = props.name || props.name_en || (feature.layer.id === '3d-buildings' ? '건물' : '장소');

                // 로딩 중 팝업 표시
                const loadingPopup = new maplibregl.Popup({ closeButton: false, className: 'poi-popup' })
                    .setLngLat(e.lngLat)
                    .setHTML('<div class="poi-info"><p>🔍 장소 데이터 매칭 중...</p></div>')
                    .addTo(this.map3D);

                try {
                    // 상세 정보 가져오기 (Reverse)
                    let response = await fetch(`https://nominatim.openstreetmap.org/reverse?format=json&lat=${e.lngLat.lat}&lon=${e.lngLat.lng}&zoom=18&addressdetails=1&extratags=1`);
                    let data = await response.json();

                    // "섞임 방지" 로직: 지도에서 클릭한 이름과 API 결과 이름이 다르면 재검색 시도
                    // 예: IFC몰을 클릭했는데 근처 음식점이 나오는 경우 등
                    if (tileName && data.name && !data.name.includes(tileName) && !tileName.includes(data.name)) {
                        console.log(`⚠️ 데이터 불일치 감지 (Tile: ${tileName}, API: ${data.name}). 재검색 수행...`);
                        const searchResp = await fetch(`https://nominatim.openstreetmap.org/search?format=json&q=${encodeURIComponent(tileName)}&lat=${e.lngLat.lat}&lon=${e.lngLat.lng}&viewbox=${e.lngLat.lng - 0.001},${e.lngLat.lat - 0.001},${e.lngLat.lng + 0.001},${e.lngLat.lat + 0.001}&bounded=1&limit=1&addressdetails=1&extratags=1`);
                        const searchData = await searchResp.json();
                        if (searchData && searchData.length > 0) {
                            data = searchData[0];
                        }
                    }

                    loadingPopup.remove();

                    const tags = data.extratags || {};
                    const addr = data.address || {};

                    const displayName = data.name || tileName;

                    // 건물명 필터링 (의미 없는 값 제외)
                    const getValidBuildingName = () => {
                        const genericTerms = ['yes', 'no', 'office', 'apartments', 'residential', 'house', 'commercial', 'retail', 'industrial', 'public', 'civic'];
                        const candidates = [
                            tags['building:name'],
                            addr.building,
                            tags.building,
                            (feature.layer.id === '3d-buildings' ? props.name : null)
                        ];

                        for (const cand of candidates) {
                            if (cand && typeof cand === 'string' && !genericTerms.includes(cand.toLowerCase()) && cand.length > 1 && cand !== displayName) {
                                return cand;
                            }
                        }
                        return null;
                    };
                    const buildingName = getValidBuildingName();

                    // 카테고리 및 아이콘 설정
                    const category = props.class || props.subclass || data.type || data.class || 'POI';
                    const categoryEmoji = {
                        'restaurant': '🍴', 'cafe': '☕', 'fast_food': '🍔', 'bar': '🍺',
                        'convenience': '🏪', 'supermarket': '🛒', 'shop': '🛍️', 'mall': '🛍️',
                        'subway': '🚇', 'bus_stop': '🚏', 'station': '🚉',
                        'bank': '🏦', 'hospital': '🏥', 'pharmacy': '💊',
                        'school': '🏫', 'park': '🌳', 'hotel': '🏨', 'theatre': '🎭',
                        'office': '🏢', 'apartments': '🏢', 'house': '🏠'
                    }[category] || '📍';

                    // 주소 정렬 (군/구 시 도 순서를 한국식으로 반전)
                    let addressStr = data.display_name.split(',').slice(0, 4).reverse().join(' ').trim();

                    // 상세 정보 조립
                    let detailHtml = '';
                    if (buildingName) detailHtml += `<p class="poi-detail">🏢 <b>소속 건물:</b> ${buildingName}</p>`;
                    if (tags.phone || tags['contact:phone']) {
                        const phone = tags.phone || tags['contact:phone'];
                        detailHtml += `<p class="poi-detail">📞 <b>전화:</b> <a href="tel:${phone}">${phone}</a></p>`;
                    }
                    if (tags.opening_hours) detailHtml += `<p class="poi-detail">⏰ <b>영업시간:</b> ${tags.opening_hours}</p>`;
                    if (tags.cuisine) detailHtml += `<p class="poi-detail">🥘 <b>메뉴/종류:</b> ${tags.cuisine}</p>`;

                    let linksHtml = '';
                    const website = tags.website || tags['contact:website'] || tags.url;
                    if (website) linksHtml += `<a href="${website}" target="_blank" class="poi-link-btn">🌐 웹사이트</a>`;

                    const insta = tags['contact:instagram'] || tags.instagram;
                    if (insta) linksHtml += `<a href="https://instagram.com/${insta.replace('@', '')}" target="_blank" class="poi-link-btn insta">📸 인스타그램</a>`;

                    new maplibregl.Popup({ closeButton: true, className: 'poi-popup' })
                        .setLngLat(e.lngLat)
                        .setHTML(`
                            <div class="poi-info">
                                <div class="poi-header">
                                    <span class="poi-emoji">${categoryEmoji}</span>
                                    <span class="poi-category">${category.toUpperCase()}</span>
                                </div>
                                <h3 class="poi-title">${displayName}</h3>
                                <p class="poi-addr">📍 ${addressStr}</p>
                                <div class="poi-details-container">
                                    ${detailHtml}
                                </div>
                                ${linksHtml ? `<div class="poi-links-container">${linksHtml}</div>` : ''}
                                <button class="poi-btn" onclick="window.webgisMap.setNavPointFromPOI(${e.lngLat.lat}, ${e.lngLat.lng}, '${displayName.replace(/'/g, "\\'")}')">🚩 여기로 길찾기</button>
                            </div>
                        `)
                        .addTo(this.map3D);

                } catch (err) {
                    new maplibregl.Popup({ closeButton: true, className: 'poi-popup' })
                        .setLngLat(e.lngLat)
                        .setHTML(`
                            <div class="poi-info">
                                <h3 class="poi-title">${name}</h3>
                                <button class="poi-btn" onclick="window.webgisMap.setNavPointFromPOI(${e.lngLat.lat}, ${e.lngLat.lng}, '${name.replace(/'/g, "\\'")}')">🚩 여기로 길찾기</button>
                            </div>
                        `)
                        .addTo(this.map3D);
                }
            });

            // 아이콘 누락 경고 해결
            this.map3D.on('styleimagemissing', (e) => {
                const id = e.id;
                // 누락된 아이콘이 있을 경우 투명 타일 처리하여 에러 방지
                const canvas = document.createElement('canvas');
                canvas.width = 1;
                canvas.height = 1;
                this.map3D.addImage(id, canvas.getContext('2d').getImageData(0, 0, 1, 1));
            });

            // 마우스 커서 변경 및 드래그 설정 고정
            this.map3D.dragPan.enable(); // 왼쪽 마우스 드래그 이동 항상 활성화
            // POI 레이어 이름을 알 수 없으므로 전체 피처 대상으로 커서 처리 (성능 고려하여 3D 건물 위주)
            this.map3D.on('mousemove', (e) => {
                const features = this.map3D.queryRenderedFeatures(e.point);
                const hasInteractive = features.some(f => f.properties.name || f.layer.id === '3d-buildings');
                this.map3D.getCanvas().style.cursor = hasInteractive ? 'pointer' : '';
            });

            this.map3D.addControl(new maplibregl.NavigationControl(), 'top-right');

            // 2.5D 네비게이션을 위한 추가 컨트롤
            this.map3D.addControl(new maplibregl.ScaleControl(), 'bottom-left');

            // 줌 레벨에 따라 pitch 자동 조정 (2.5D 네비게이션 효과)
            // 줌 레벨에 따라 pitch 자동 조정 기능은 렌더링 루프 문제를 일으키므로 제거함
            // this.map3D.on('zoom', () => { ... });
        } else if (this.map3D) {
            this.map3D.resize();
            const targetZoom = Math.max(zoom, 13);
            const targetPitch = Math.min(50 + (targetZoom - 13) * 2, 65);
            this.map3D.jumpTo({
                center: lonLat,
                zoom: targetZoom,
                pitch: targetPitch,
                bearing: 0
            });
        }

        // 선택 위치 마커 표시
        if (targetLat !== null && targetLon !== null && this.map3D && window.maplibregl) {
            if (this.map3DMarker) {
                this.map3DMarker.remove();
            }
            const el = document.createElement('div');
            el.className = 'map3d-marker';
            this.map3DMarker = new maplibregl.Marker(el)
                .setLngLat([targetLon, targetLat])
                .addTo(this.map3D);
        }

        this.showToast('🧱 3D View 모드가 활성화되었습니다. 마우스로 회전/이동해보세요.', 'info');
    }

    // 3D View 비활성화
    deactivate3DView() {
        this.is3DActive = false;
        const map3dEl = document.getElementById('map3d');
        if (map3dEl) {
            map3dEl.style.display = 'none';
        }
        const mapEl = document.getElementById('map');
        if (mapEl) {
            mapEl.style.visibility = '';
        }
        if (this.map3DMarker) {
            this.map3DMarker.remove();
            this.map3DMarker = null;
        }
    }

    // Street View 표시 (지도 위에 직접 표시)
    async showStreetView(lat, lon) {
        const panel = document.getElementById('streetViewPanel');
        const loading = document.getElementById('streetViewLoading');
        const empty = document.getElementById('streetViewEmpty');
        const viewer = document.getElementById('mapillaryViewer');
        const info = document.getElementById('streetViewInfo');

        if (!panel || !this.map) return;

        panel.style.display = 'block';
        if (info) info.style.display = 'none';
        if (loading) loading.style.display = 'block';
        if (empty) empty.style.display = 'none';
        if (viewer) viewer.style.display = 'none';

        try {
            // 지도 위에 Street View 오버레이 표시
            const coordinate = fromLonLat([lon, lat]);

            // 기존 오버레이 제거
            if (this.streetViewOverlay) {
                this.map.removeOverlay(this.streetViewOverlay);
                this.streetViewOverlay = null;
            }

            // 기존 마커 제거
            if (this.streetViewMarker) {
                this.vectorSource.removeFeature(this.streetViewMarker);
                this.streetViewMarker = null;
            }

            // Street View 마커 추가
            const markerFeature = new Feature({
                geometry: new Point(coordinate),
                type: 'streetview'
            });

            markerFeature.setStyle(new Style({
                image: new Icon({
                    src: 'data:image/svg+xml;base64,' + btoa(`
                        <svg xmlns="http://www.w3.org/2000/svg" width="40" height="40" viewBox="0 0 24 24" fill="#4facfe">
                            <path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/>
                            <circle cx="12" cy="9" r="3" fill="#00f2fe"/>
                        </svg>
                    `),
                    scale: 1.2,
                    anchor: [0.5, 1]
                })
            }));

            this.vectorSource.addFeature(markerFeature);
            this.streetViewMarker = markerFeature;

            // Street View 오버레이 패널 생성
            const overlayElement = document.createElement('div');
            overlayElement.className = 'streetview-overlay';
            overlayElement.style.width = '400px';
            overlayElement.style.maxWidth = '90vw';
            overlayElement.style.background = 'white';
            overlayElement.style.borderRadius = '12px';
            overlayElement.style.boxShadow = '0 8px 32px rgba(0, 0, 0, 0.2)';
            overlayElement.style.overflow = 'hidden';
            overlayElement.style.zIndex = '1000';

            // Street View 컨텐츠
            const streetViewContent = await this.createStreetViewContent(lat, lon);
            overlayElement.appendChild(streetViewContent);

            // 오버레이 생성 및 지도에 추가
            this.streetViewOverlay = new Overlay({
                element: overlayElement,
                positioning: 'bottom-center',
                stopEvent: true,
                offset: [0, -20],
                autoPan: {
                    animation: {
                        duration: 250
                    },
                    margin: 80 // 오버레이가 잘리지 않도록 여백 확보
                }
            });

            this.map.addOverlay(this.streetViewOverlay);
            this.streetViewOverlay.setPosition(coordinate);

            // 현재 Street View 위치 저장
            this.currentStreetViewLocation = { lat, lon };

            // 지도 중심을 약간 이동시켜 카드가 잘 보이도록 조정
            this.adjustMapForStreetViewOverlay(coordinate);

            // 지도 이동 시 Street View 업데이트 (연동)
            this.setupStreetViewMapSync();

            if (loading) loading.style.display = 'none';

        } catch (error) {
            console.error('Street View 로드 오류:', error);
            if (loading) loading.style.display = 'none';
            if (empty) empty.style.display = 'block';
        }
    }

    // Street View 컨텐츠 생성
    async createStreetViewContent(lat, lon) {
        const container = document.createElement('div');

        // 헤더
        const header = document.createElement('div');
        header.style.padding = '1rem';
        header.style.background = 'linear-gradient(135deg, #4facfe 0%, #00f2fe 100%)';
        header.style.color = 'white';
        header.style.display = 'flex';
        header.style.justifyContent = 'space-between';
        header.style.alignItems = 'center';

        const title = document.createElement('h4');
        title.textContent = '🛣️ Street View';
        title.style.margin = '0';
        title.style.fontSize = '1.1rem';
        title.style.fontWeight = '600';

        const closeBtn = document.createElement('button');
        closeBtn.textContent = '✖';
        closeBtn.style.background = 'rgba(255, 255, 255, 0.2)';
        closeBtn.style.border = 'none';
        closeBtn.style.color = 'white';
        closeBtn.style.borderRadius = '50%';
        closeBtn.style.width = '28px';
        closeBtn.style.height = '28px';
        closeBtn.style.cursor = 'pointer';
        closeBtn.style.fontSize = '1rem';
        closeBtn.onclick = () => {
            this.closeStreetView();
        };

        header.appendChild(title);
        header.appendChild(closeBtn);

        // 본문
        const body = document.createElement('div');
        body.className = 'streetview-overlay-body';
        body.style.padding = '1.5rem';

        const description = document.createElement('p');
        description.textContent = '이 위치 주변에서 찾은 거리/위치 이미지입니다. (근처 사진이 없으면 유사한 예시 이미지를 표시합니다)';
        description.style.margin = '0 0 1rem 0';
        description.style.color = '#666';
        description.style.fontSize = '0.9rem';

        // 좌표 정보
        const coordInfo = document.createElement('div');
        coordInfo.style.padding = '0.75rem';
        coordInfo.style.background = 'rgba(79, 172, 254, 0.1)';
        coordInfo.style.borderRadius = '8px';
        coordInfo.style.fontSize = '0.85rem';
        coordInfo.style.color = '#555';
        coordInfo.innerHTML = `
            <strong>📍 위치</strong><br>
            위도: ${lat.toFixed(6)}<br>
            경도: ${lon.toFixed(6)}
        `;

        // 3D View로 보기 버튼
        const view3DButton = document.createElement('button');
        view3DButton.textContent = '🧱 3D View로 보기';
        view3DButton.className = 'inline-btn view-3d-btn';
        view3DButton.style.marginTop = '0.75rem';
        view3DButton.onclick = () => {
            const layerSelect = document.getElementById('layerSelect');
            if (layerSelect) {
                layerSelect.value = '3d';
            }
            this.activate3DView(lat, lon);
        };

        // 거리 사진 영역
        const imagesContainer = document.createElement('div');
        imagesContainer.className = 'streetview-images';
        imagesContainer.style.marginTop = '1rem';
        imagesContainer.style.padding = '0.75rem';
        imagesContainer.style.borderRadius = '8px';
        imagesContainer.style.background = 'rgba(148, 163, 184, 0.12)';
        imagesContainer.style.fontSize = '0.85rem';
        imagesContainer.style.color = '#475569';
        imagesContainer.textContent = '이 위치 주변의 거리 사진을 불러오는 중입니다...';

        body.appendChild(description);
        body.appendChild(coordInfo);
        body.appendChild(view3DButton);
        body.appendChild(imagesContainer);

        container.appendChild(header);
        container.appendChild(body);

        // 비동기로 거리 사진 로드
        this.fillStreetViewImages(lat, lon, imagesContainer);

        return container;
    }

    // Street View용 거리 사진 로드 (Wikimedia 기반)
    async fillStreetViewImages(lat, lon, container) {
        if (!container) return;

        try {
            container.textContent = '이 위치 주변의 거리 사진을 불러오는 중입니다...';

            let images = [];

            // 가까운 범위부터 Wikimedia 거리 사진 검색
            images = await this.searchWikimediaImages(lat, lon, 500);
            if (!images || images.length === 0) {
                images = await this.searchWikimediaImages(lat, lon, 2000);
            }
            if (!images || images.length === 0) {
                images = await this.searchWikimediaImages(lat, lon, 5000);
            }

            container.innerHTML = '';

            if (!images || images.length === 0) {
                container.textContent = '이 위치 주변에서 보여줄 수 있는 거리/위치 이미지를 찾을 수 없습니다.';
                return;
            }

            // 가장 가까운 사진 순으로 정렬
            images.sort((a, b) => (a.distance || 0) - (b.distance || 0));

            const main = images[0];

            const mainWrapper = document.createElement('div');
            mainWrapper.style.borderRadius = '10px';
            mainWrapper.style.overflow = 'hidden';
            mainWrapper.style.boxShadow = '0 4px 12px rgba(15,23,42,0.15)';
            mainWrapper.style.marginBottom = '0.75rem';

            const mainImg = document.createElement('img');
            mainImg.src = main.url;
            mainImg.alt = main.title || 'Street image';
            mainImg.style.width = '100%';
            mainImg.style.display = 'block';
            mainImg.style.cursor = 'pointer';
            mainImg.onclick = () => this.showImageViewer(main, mainImg);

            mainWrapper.appendChild(mainImg);

            const caption = document.createElement('div');
            caption.style.padding = '0.5rem 0.75rem';
            caption.style.background = 'rgba(15,23,42,0.03)';
            caption.style.fontSize = '0.8rem';
            const isFallback = !!main.isFallback;
            const isFromWikimedia = !isFallback && !!main.fullUrl && main.fullUrl.includes('wikimedia.org');
            const distanceText = !isFallback && typeof main.distance === 'number'
                ? `거리 약 ${Math.round(main.distance)}m`
                : '위치 기반 이미지';
            const sourceText = isFallback
                ? '예시 거리 이미지 (실제 위치 아님)'
                : (isFromWikimedia ? 'Wikimedia Commons' : '공개 이미지 서비스');

            caption.innerHTML = `📷 선택된 거리/위치 이미지<br><span style="opacity:.8;">${sourceText}${distanceText ? `, ${distanceText}` : ''}</span>`;

            mainWrapper.appendChild(caption);
            container.appendChild(mainWrapper);

            // 추가 썸네일 (최대 12개까지 표시)
            const thumbs = images.slice(1, 13);
            if (thumbs.length > 0) {
                const thumbsWrap = document.createElement('div');
                thumbsWrap.className = 'streetview-thumbs-grid';

                thumbs.forEach(img => {
                    const thumb = document.createElement('img');
                    thumb.src = img.url;
                    thumb.alt = img.title || 'Street image';
                    thumb.onclick = () => this.showImageViewer(img, thumb);
                    thumbsWrap.appendChild(thumb);
                });

                container.appendChild(thumbsWrap);
            }
        } catch (error) {
            console.error('Street View 이미지 로드 오류:', error);
            container.textContent = '거리 사진을 불러오는 중 오류가 발생했습니다.';
        }
    }

    // Street View 카드가 잘 보이도록 지도를 약간 이동
    adjustMapForStreetViewOverlay(coordinate) {
        try {
            if (!this.map) return;
            const view = this.map.getView();
            const size = this.map.getSize();
            if (!view || !size) return;

            const pixel = this.map.getPixelFromCoordinate(coordinate);
            if (!pixel) return;

            const [width, height] = size;
            // 마커는 화면 가운데보다 약간 위쪽에 두고,
            // 카드가 그 아래로 내려오도록 y좌표를 살짝 올립니다.
            const targetPixel = [
                pixel[0],
                pixel[1] - height * 0.18
            ];

            const newCenter = this.map.getCoordinateFromPixel(targetPixel);
            if (!newCenter) return;

            view.animate({
                center: newCenter,
                zoom: Math.max(view.getZoom(), 15),
                duration: 500
            });
        } catch (e) {
            console.error('Street View 카드 위치 조정 중 오류:', e);
        }
    }

    // Street View와 지도 연동 설정
    setupStreetViewMapSync() {
        // 예전에는 지도 이동/줌 변경 시 Street View 위치를 함께 이동시켰지만,
        // 사용자가 지도를 패닝할 때마다 이미지를 재검색하는 문제가 있어 비활성화한다.
        // 이제 Street View는 "처음 클릭한 위치"에 고정되고,
        // 다른 위치를 보려면 지도를 클릭해서 새 Street View를 여는 방식으로 동작한다.

        // 기존 리스너가 남아 있다면 제거만 수행
        if (this.mapMoveListener) {
            unByKey(this.mapMoveListener);
            this.mapMoveListener = null;
        }
    }

    // Street View 위치 업데이트 (지도 이동에 따라)
    updateStreetViewLocation(lat, lon) {
        if (!this.streetViewOverlay || !this.streetViewMarker) return;

        // 위치가 크게 변경되지 않았으면 스킵 (너무 자주 업데이트 방지)
        if (this.currentStreetViewLocation) {
            const distance = Math.sqrt(
                Math.pow(lat - this.currentStreetViewLocation.lat, 2) +
                Math.pow(lon - this.currentStreetViewLocation.lon, 2)
            );

            // 0.001도 (약 100m) 이상 이동했을 때만 업데이트
            if (distance < 0.001) return;
        }

        this.currentStreetViewLocation = { lat, lon };
        const coordinate = fromLonLat([lon, lat]);

        // 마커 위치 업데이트
        this.streetViewMarker.getGeometry().setCoordinates(coordinate);

        // 오버레이 위치 업데이트
        this.streetViewOverlay.setPosition(coordinate);

        // 오버레이 내용 업데이트 (새로운 링크)
        const overlayElement = this.streetViewOverlay.getElement();
        if (overlayElement) {
            const coordInfo = overlayElement.querySelector('div[style*="background: rgba(79, 172, 254, 0.1)"]');
            if (coordInfo) {
                coordInfo.innerHTML = `
                    <strong>📍 위치</strong><br>
                    위도: ${lat.toFixed(6)}<br>
                    경도: ${lon.toFixed(6)}
                `;
            }

            const imagesContainer = overlayElement.querySelector('.streetview-images');
            if (imagesContainer) {
                this.fillStreetViewImages(lat, lon, imagesContainer);
            }
        }

        console.log('🔄 Street View 위치 업데이트:', lat, lon);
    }

    // Street View 닫기
    closeStreetView() {
        if (this.streetViewOverlay) {
            this.map.removeOverlay(this.streetViewOverlay);
            this.streetViewOverlay = null;
        }
        if (this.streetViewMarker) {
            this.vectorSource.removeFeature(this.streetViewMarker);
            this.streetViewMarker = null;
        }
        if (this.mapMoveListener) {
            unByKey(this.mapMoveListener);
            this.mapMoveListener = null;
        }
        this.currentStreetViewLocation = null;
    }

    // 오픈소스 Street View 로드 (API 키/토큰 불필요, iframe 제한 우회)
    async loadOpenSourceStreetView(lat, lon, container) {
        try {
            if (!container) return false;

            container.innerHTML = '';
            container.style.display = 'block';
            container.style.width = '100%';
            container.style.minHeight = '300px';
            container.style.borderRadius = '8px';
            container.style.padding = '1.5rem';
            container.style.background = 'linear-gradient(135deg, rgba(79, 172, 254, 0.1) 0%, rgba(0, 242, 254, 0.1) 100%)';

            // 제목
            const title = document.createElement('h4');
            title.textContent = '🛣️ 오픈소스 Street View';
            title.style.margin = '0 0 0.5rem 0';
            title.style.color = '#4facfe';
            title.style.fontSize = '1.2rem';
            title.style.fontWeight = '600';

            // 설명
            const description = document.createElement('p');
            description.textContent = 'Mapillary는 오픈소스 커뮤니티 기반 스트리트 뷰 서비스입니다. 아래 버튼을 클릭하여 새 창에서 Street View를 확인하세요.';
            description.style.margin = '0 0 1.5rem 0';
            description.style.color = '#666';
            description.style.fontSize = '0.95rem';
            description.style.lineHeight = '1.6';

            // 링크 버튼
            const linkButton = document.createElement('a');
            const mapillaryUrl = `https://www.mapillary.com/app/?lat=${lat}&lng=${lon}&z=17&focus=photo`;
            linkButton.href = mapillaryUrl;
            linkButton.target = '_blank';
            linkButton.rel = 'noopener noreferrer';
            linkButton.textContent = '🌍 Mapillary에서 Street View 보기';
            linkButton.style.display = 'inline-block';
            linkButton.style.padding = '1rem 2rem';
            linkButton.style.background = 'linear-gradient(135deg, #4facfe 0%, #00f2fe 100%)';
            linkButton.style.color = 'white';
            linkButton.style.textDecoration = 'none';
            linkButton.style.borderRadius = '10px';
            linkButton.style.fontWeight = '600';
            linkButton.style.fontSize = '1rem';
            linkButton.style.transition = 'all 0.3s ease';
            linkButton.style.cursor = 'pointer';
            linkButton.style.boxShadow = '0 4px 15px rgba(79, 172, 254, 0.3)';
            linkButton.style.marginBottom = '1rem';

            linkButton.onmouseenter = () => {
                linkButton.style.transform = 'translateY(-2px)';
                linkButton.style.boxShadow = '0 6px 20px rgba(79, 172, 254, 0.4)';
            };
            linkButton.onmouseleave = () => {
                linkButton.style.transform = 'translateY(0)';
                linkButton.style.boxShadow = '0 4px 15px rgba(79, 172, 254, 0.3)';
            };

            // 좌표 정보
            const coordInfo = document.createElement('div');
            coordInfo.style.marginTop = '1rem';
            coordInfo.style.padding = '0.75rem';
            coordInfo.style.background = 'rgba(255, 255, 255, 0.7)';
            coordInfo.style.borderRadius = '8px';
            coordInfo.style.fontSize = '0.9rem';
            coordInfo.style.color = '#555';
            coordInfo.style.border = '1px solid rgba(79, 172, 254, 0.2)';
            coordInfo.innerHTML = `
                <strong>📍 위치 정보</strong><br>
                위도: ${lat.toFixed(6)}<br>
                경도: ${lon.toFixed(6)}
            `;

            // 안내 메시지
            const note = document.createElement('div');
            note.style.marginTop = '1rem';
            note.style.padding = '0.75rem';
            note.style.background = 'rgba(79, 172, 254, 0.1)';
            note.style.borderRadius = '6px';
            note.style.fontSize = '0.85rem';
            note.style.color = '#4facfe';
            note.style.borderLeft = '3px solid #4facfe';
            note.innerHTML = '💡 <strong>팁:</strong> 버튼을 클릭하면 새 창에서 Mapillary Street View가 열립니다.';

            container.appendChild(title);
            container.appendChild(description);
            container.appendChild(linkButton);
            container.appendChild(coordInfo);
            container.appendChild(note);

            console.log('🌍 오픈소스 Street View 링크 생성:', lat, lon);
            return true;
        } catch (error) {
            console.error('오픈소스 Street View 로드 오류:', error);
            return false;
        }
    }

    // 도구 활성화
    activateTool(toolType) {
        this.deactivateCurrentTool();

        // 버튼 상태 업데이트
        document.querySelectorAll('.tool-btn').forEach(btn => {
            btn.classList.remove('active');
        });

        const buttonMap = {
            'distance': 'measureDistance',
            'area': 'measureArea',
            'marker': 'addMarker'
        };

        if (buttonMap[toolType]) {
            document.getElementById(buttonMap[toolType]).classList.add('active');
        }

        this.currentTool = toolType;

        switch (toolType) {
            case 'distance':
                this.startDistanceMeasurement();
                break;
            case 'area':
                this.startAreaMeasurement();
                break;
            case 'marker':
                // 마커 모드 활성화 (클릭 이벤트는 이미 설정됨)
                break;
        }
        this.updatePanelVisibility();
    }

    // 현재 도구 비활성화
    deactivateCurrentTool() {
        if (this.draw) {
            this.map.removeInteraction(this.draw);
            this.draw = null;
        }
        if (this.snap) {
            this.map.removeInteraction(this.snap);
            this.snap = null;
        }
        if (this.modify) {
            this.map.removeInteraction(this.modify);
            this.modify = null;
        }
        if (this.measurementListener) {
            unByKey(this.measurementListener);
            this.measurementListener = null;
        }
        if (this.distanceOverlay) {
            this.map.removeOverlay(this.distanceOverlay);
            this.distanceOverlay = null;
        }

        this.currentTool = null;
        this.updatePanelVisibility();
    }

    // 거리 측정 시작
    startDistanceMeasurement() {
        console.log('📏 거리 측정 시작');

        // 사용자 안내 메시지
        document.getElementById('measurementResult').innerHTML =
            '<div class="measurement-guide">지도에서 두 지점을 클릭하여 거리를 측정하세요.</div>';

        // 측정 결과 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('measurement-panel', '거리 측정을 시작합니다!');

        // 기존 인터랙션 제거
        this.deactivateCurrentTool();

        // Draw 인터랙션 생성
        this.draw = new Draw({
            source: this.vectorSource,
            type: 'LineString',
            style: new Style({
                stroke: new Stroke({
                    color: '#00ff00',
                    width: 3,
                    lineDash: [5, 5]
                }),
                image: new CircleStyle({
                    radius: 8,
                    fill: new Fill({
                        color: '#00ff00'
                    }),
                    stroke: new Stroke({
                        color: '#ffffff',
                        width: 2
                    })
                })
            })
        });

        // 인터랙션을 지도에 추가
        this.map.addInteraction(this.draw);
        console.log('✅ Draw 인터랙션 추가됨');

        // 그리기 시작 이벤트
        this.draw.on('drawstart', (event) => {
            console.log('🎯 그리기 시작됨');
            document.getElementById('measurementResult').innerHTML =
                '<div class="measurement-guide">두 번째 지점을 클릭하세요.</div>';
            // 라이브 툴팁 준비
            if (!this.liveTooltipOverlay) {
                const el = document.createElement('div');
                el.className = 'toast';
                el.style.pointerEvents = 'none';
                this.liveTooltipOverlay = new Overlay({ element: el, offset: [10, -10], positioning: 'bottom-left' });
                this.map.addOverlay(this.liveTooltipOverlay);
            }
            const sketch = event.feature;
            sketch.getGeometry().on('change', (e) => {
                const geom = e.target;
                const coords = geom.getCoordinates();
                if (coords && coords.length >= 2) {
                    const len = getLength(geom);
                    this.liveTooltipOverlay.getElement().textContent = this.formatDistance(len);
                    this.liveTooltipOverlay.setPosition(coords[coords.length - 1]);
                    // 마지막 구간 배지
                    const lastSeg = [coords[coords.length - 2], coords[coords.length - 1]];
                    const mid = [(lastSeg[0][0] + lastSeg[1][0]) / 2, (lastSeg[0][1] + lastSeg[1][1]) / 2];
                    const segLen = getLength(new LineString(lastSeg));
                    if (!this.segmentOverlay) {
                        const el = document.createElement('div');
                        el.className = 'toast';
                        el.style.pointerEvents = 'none';
                        this.segmentOverlay = new Overlay({ element: el, offset: [0, -10], positioning: 'bottom-center' });
                        this.map.addOverlay(this.segmentOverlay);
                    }
                    this.segmentOverlay.getElement().textContent = this.formatDistance(segLen);
                    this.segmentOverlay.setPosition(mid);
                    // 패널 자동 주목
                    const panel = document.getElementById('measurementResult');
                    if (panel) {
                        panel.classList.remove('panel-highlight');
                        void panel.offsetWidth;
                        panel.classList.add('panel-highlight');
                    }
                }
            });
        });

        // 그리기 완료 이벤트
        this.draw.on('drawend', (event) => {
            console.log('✅ 그리기 완료됨');
            const feature = event.feature;
            const geometry = feature.getGeometry();
            const coordinates = geometry.getCoordinates();

            console.log('📍 좌표 개수:', coordinates.length);
            console.log('📍 좌표:', coordinates);

            if (coordinates.length >= 2) {
                const length = getLength(geometry);
                console.log('📏 계산된 거리:', length);

                // 측정 결과를 피처에 저장
                feature.set('type', 'measurement');
                feature.set('measurement', 'distance');
                feature.set('value', length);
                feature.set('coordinates', coordinates);

                // 측정 결과를 배열에 저장
                const resultText = this.formatDistance(length);
                this.measurementResults.push({
                    type: 'distance',
                    value: length,
                    text: resultText,
                    coordinates: coordinates
                });

                console.log('💾 측정 결과 추가됨:', resultText);

                // 성공 메시지 표시
                document.getElementById('measurementResult').innerHTML =
                    `<div class="measurement-success">✅ ${resultText} 측정 완료!</div>`;

                // 측정 결과 표시 업데이트
                setTimeout(() => {
                    this.updateMeasurementDisplay();
                }, 1000);

                // 도구 유지(연속 측정), 오버레이 제거
                if (this.liveTooltipOverlay) {
                    this.map.removeOverlay(this.liveTooltipOverlay);
                    this.liveTooltipOverlay = null;
                }
                if (this.segmentOverlay) {
                    this.map.removeOverlay(this.segmentOverlay);
                    this.segmentOverlay = null;
                }
                // 라이브 툴팁 제거
                if (this.liveTooltipOverlay) {
                    this.map.removeOverlay(this.liveTooltipOverlay);
                    this.liveTooltipOverlay = null;
                }
            } else {
                console.log('❌ 좌표가 부족합니다');
                document.getElementById('measurementResult').innerHTML =
                    '<div class="measurement-guide">두 개 이상의 지점을 클릭해주세요.</div>';
            }
        });

        // 단축키: Enter/ESC/Backspace, 패널 버튼과 연동
        const keyHandler = (e) => {
            if (e.key === 'Enter') {
                this.draw.finishDrawing?.();
            } else if (e.key === 'Escape') {
                this.deactivateCurrentTool();
                if (this.liveTooltipOverlay) { this.map.removeOverlay(this.liveTooltipOverlay); this.liveTooltipOverlay = null; }
            } else if (e.key === 'Backspace') {
                this.draw.removeLastPoint?.();
            }
        };
        document.addEventListener('keydown', keyHandler, { once: false });
        const finishBtn = document.getElementById('finishMeasure');
        const cancelBtn = document.getElementById('cancelMeasure');
        if (finishBtn) finishBtn.onclick = () => this.draw.finishDrawing?.();
        if (cancelBtn) cancelBtn.onclick = () => { this.deactivateCurrentTool(); if (this.liveTooltipOverlay) { this.map.removeOverlay(this.liveTooltipOverlay); this.liveTooltipOverlay = null; } };
    }

    // 거리 포맷팅
    formatDistance(length) {
        if (length < 1000) {
            return `거리: ${length.toFixed(1)} m`;
        } else if (length < 100000) {
            return `거리: ${(length / 1000).toFixed(3)} km`;
        } else {
            return `거리: ${(length / 1000).toFixed(1)} km`;
        }
    }

    // 면적 측정 시작
    startAreaMeasurement() {
        console.log('📐 면적 측정 시작');

        // 사용자 안내 메시지
        document.getElementById('measurementResult').innerHTML =
            '<div class="measurement-guide">지도에서 다각형을 그려 면적을 측정하세요.</div>';

        // 측정 결과 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('measurement-panel', '면적 측정을 시작합니다!');

        this.draw = new Draw({
            source: this.vectorSource,
            type: 'Polygon',
            style: this.getMeasurementStyle()
        });

        this.snap = new Snap({ source: this.vectorSource });
        this.modify = new Modify({ source: this.vectorSource });

        this.map.addInteraction(this.draw);
        this.map.addInteraction(this.snap);
        this.map.addInteraction(this.modify);

        this.measurementListener = this.draw.on('drawend', (event) => {
            console.log('✅ 면적 측정 완료');
            const feature = event.feature;
            const geometry = feature.getGeometry();
            const area = getArea(geometry);

            console.log('📐 계산된 면적:', area);

            // 측정 결과를 피처에 저장
            feature.set('type', 'measurement');
            feature.set('measurement', 'area');
            feature.set('value', area);

            // 측정 결과를 배열에 저장
            const resultText = this.formatArea(area);
            this.measurementResults.push({
                type: 'area',
                value: area,
                text: resultText
            });

            console.log('💾 측정 결과 추가됨:', resultText);

            // 측정 결과 표시 업데이트
            this.updateMeasurementDisplay();

            // 성공 메시지 표시
            document.getElementById('measurementResult').innerHTML =
                `<div class="measurement-success">✅ ${resultText} 측정 완료!</div>`;

            // 측정 완료 후 도구 비활성화
            setTimeout(() => {
                this.deactivateCurrentTool();
                document.getElementById('measureArea').classList.remove('active');
                this.updateMeasurementDisplay();
            }, 3000);
        });
    }

    // 면적 포맷팅
    formatArea(area) {
        if (area < 1000000) {
            return `면적: ${(area / 10000).toFixed(2)} ha`;
        } else {
            return `면적: ${(area / 1000000).toFixed(3)} km²`;
        }
    }

    // 측정 결과 표시 업데이트
    updateMeasurementDisplay() {
        const resultElement = document.getElementById('measurementResult');
        if (this.measurementResults.length === 0) {
            resultElement.innerHTML = '측정 결과가 없습니다.';
            return;
        }

        let html = '<div class="measurement-list">';
        this.measurementResults.forEach((result, index) => {
            html += `<div class="measurement-item">
                <span class="measurement-text">${result.text}</span>
                <button class="remove-measurement" onclick="window.webgisMap.removeMeasurement(${index})">×</button>
            </div>`;
        });
        html += '</div>';

        resultElement.innerHTML = html;

        // 자동 스크롤 및 하이라이트: 최근 결과로 스크롤
        const container = resultElement;
        const lastItem = container.querySelector('.measurement-item:last-child');
        if (lastItem) {
            lastItem.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
            container.classList.remove('panel-highlight');
            void container.offsetWidth; // reflow to restart animation
            container.classList.add('panel-highlight');
        }
        // 측정 이력도 동기 스크롤
        this.renderMeasureHistory();
        this.updatePanelVisibility();
    }

    // 패널 가시성 업데이트 (필요할 때만 표시)
    updatePanelVisibility() {
        // 즐겨찾기 목록 확인
        const hasFavorites = this.favorites && this.favorites.length > 0;

        const isMeasuring = this.currentTool === 'distance' || this.currentTool === 'area';
        const hasMeasurements = this.measurementResults && this.measurementResults.length > 0;

        // 측정 관련 패널 (측정 중이거나 결과가 있을 때)
        const measureSettingsPanel = document.getElementById('measureSettingsPanel');
        const measurementPanel = document.getElementById('measurementPanel');
        const legendPanel = document.getElementById('legendPanel');

        if (measureSettingsPanel) {
            measureSettingsPanel.style.display = isMeasuring ? 'block' : 'none';
        }
        if (measurementPanel) {
            measurementPanel.style.display = (isMeasuring || hasMeasurements) ? 'block' : 'none';
        }
        if (legendPanel) {
            legendPanel.style.display = (isMeasuring || hasMeasurements) ? 'block' : 'none';
        }

        // 즐겨찾기 패널
        const favoritesPanel = document.getElementById('favoritesPanel');
        if (favoritesPanel) {
            favoritesPanel.style.display = hasFavorites ? 'block' : 'none';
        }
    }

    renderMeasureHistory() {
        const el = document.getElementById('measureHistoryList');
        if (!el) return;
        if (!this.measurementHistory.length) {
            el.innerHTML = '<div class="empty">이력이 없습니다.</div>';
            return;
        }
        el.innerHTML = this.measurementHistory.slice(0, 10).map(h => `
            <div class="measurement-item">
                <span class="measurement-text">${h.text}</span>
                <small style="margin-left:6px;opacity:.7;">${h.when.slice(11, 16)}</small>
            </div>
        `).join('');
    }

    // 개별 측정 결과 삭제
    removeMeasurement(index) {
        this.measurementResults.splice(index, 1);
        this.updateMeasurementDisplay();
    }

    // 마커 추가
    addMarker(coordinate) {
        console.log('📍 마커 추가:', coordinate);

        const marker = new Feature({
            geometry: new Point(coordinate)
        });

        marker.set('type', 'marker');
        marker.setStyle(this.getMarkerStyle());

        this.vectorSource.addFeature(marker);

        // 성공 메시지 표시
        const lonLat = transform(coordinate, 'EPSG:3857', 'EPSG:4326');
        document.getElementById('measurementResult').innerHTML =
            `<div class="measurement-success">✅ 마커가 추가되었습니다! (${lonLat[1].toFixed(4)}, ${lonLat[0].toFixed(4)})</div>`;

        // 측정 결과 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('measurement-panel', '마커가 추가되었습니다!');

        console.log('✅ 마커 추가 완료');
    }

    // 모든 피처 삭제
    clearAllFeatures() {
        // 확인 대화상자 표시
        if (confirm('모든 측정 데이터와 마커를 삭제하시겠습니까?')) {
            this.vectorSource.clear();
            this.measurementResults = [];
            this.updateMeasurementDisplay();

            // 검색 결과 마커도 함께 삭제
            this.clearAllSearchResultMarkers();

            // 즐겨찾기 마커도 함께 삭제
            this.clearAllFavoriteMarkers();

            // 버튼 상태 초기화
            document.querySelectorAll('.tool-btn').forEach(btn => {
                btn.classList.remove('active');
            });

            // 현재 도구 비활성화
            this.deactivateCurrentTool();
            this.updatePanelVisibility();
        }
    }

    // 데이터 내보내기
    exportData() {
        const features = this.vectorSource.getFeatures();
        if (features.length === 0) {
            alert('내보낼 데이터가 없습니다.');
            return;
        }

        const exportData = {
            type: 'FeatureCollection',
            features: features.map(feature => {
                const geometry = feature.getGeometry();
                const coordinates = geometry.getCoordinates();

                // 좌표계 변환 (EPSG:3857 -> EPSG:4326)
                const transformedCoords = this.transformCoordinates(coordinates, geometry.getType());

                return {
                    type: 'Feature',
                    geometry: {
                        type: geometry.getType(),
                        coordinates: transformedCoords
                    },
                    properties: {
                        type: feature.get('type'),
                        measurement: feature.get('measurement'),
                        value: feature.get('value')
                    }
                };
            }),
            measurements: this.measurementResults
        };

        const dataStr = JSON.stringify(exportData, null, 2);
        const dataBlob = new Blob([dataStr], { type: 'application/json' });
        const url = URL.createObjectURL(dataBlob);

        const link = document.createElement('a');
        link.href = url;
        link.download = `webgis_data_${new Date().toISOString().slice(0, 10)}.json`;
        link.click();

        URL.revokeObjectURL(url);
    }

    // 좌표 변환
    transformCoordinates(coordinates, geometryType) {
        if (geometryType === 'Point') {
            return transform(coordinates, 'EPSG:3857', 'EPSG:4326');
        } else if (geometryType === 'LineString') {
            return coordinates.map(coord => transform(coord, 'EPSG:3857', 'EPSG:4326'));
        } else if (geometryType === 'Polygon') {
            return coordinates.map(ring =>
                ring.map(coord => transform(coord, 'EPSG:3857', 'EPSG:4326'))
            );
        }
        return coordinates;
    }

    // 피처별 스타일 적용
    getFeatureStyle(feature) {
        const type = feature.get('type');

        if (type === 'measurement') {
            const measurement = feature.get('measurement');
            const value = feature.get('value');

            if (measurement === 'distance') {
                return this.getDistanceStyle(value);
            } else if (measurement === 'area') {
                return this.getAreaStyle(value);
            }
        } else if (type === 'marker') {
            return this.getMarkerStyle();
        }

        return this.getDefaultStyle();
    }

    // 기본 스타일
    getDefaultStyle() {
        return new Style({
            stroke: new Stroke({
                color: '#ff4757',
                width: 2
            }),
            fill: new Fill({
                color: 'rgba(255, 71, 87, 0.2)'
            }),
            image: new CircleStyle({
                radius: 7,
                fill: new Fill({
                    color: '#ff4757'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                })
            })
        });
    }

    // 거리 측정 그리기 스타일
    getDistanceDrawingStyle() {
        return new Style({
            stroke: new Stroke({
                color: '#2ed573',
                width: 3,
                lineDash: [5, 5]
            }),
            image: new CircleStyle({
                radius: 6,
                fill: new Fill({
                    color: '#2ed573'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                })
            })
        });
    }

    // 측정용 스타일
    getMeasurementStyle() {
        return new Style({
            stroke: new Stroke({
                color: '#2ed573',
                width: 3
            }),
            fill: new Fill({
                color: 'rgba(46, 213, 115, 0.2)'
            }),
            image: new CircleStyle({
                radius: 6,
                fill: new Fill({
                    color: '#2ed573'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                })
            })
        });
    }

    // 거리 측정 스타일
    getDistanceStyle(length) {
        return new Style({
            stroke: new Stroke({
                color: '#2ed573',
                width: 3
            }),
            image: new CircleStyle({
                radius: 6,
                fill: new Fill({
                    color: '#2ed573'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                })
            }),
            text: new Text({
                text: this.formatDistance(length),
                font: '14px Arial',
                fill: new Fill({
                    color: '#2ed573'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                }),
                offsetY: -10
            })
        });
    }

    // 면적 측정 스타일
    getAreaStyle(area) {
        return new Style({
            stroke: new Stroke({
                color: '#2ed573',
                width: 3
            }),
            fill: new Fill({
                color: 'rgba(46, 213, 115, 0.2)'
            }),
            text: new Text({
                text: this.formatArea(area),
                font: '14px Arial',
                fill: new Fill({
                    color: '#2ed573'
                }),
                stroke: new Stroke({
                    color: '#fff',
                    width: 2
                }),
                offsetY: 0
            })
        });
    }

    // 마커 스타일
    getMarkerStyle() {
        return new Style({
            image: new Icon({
                anchor: [0.5, 1],
                src: 'data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="%23ff4757"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/></svg>'
            })
        });
    }

    // 검색 결과 마커 추가
    addSearchResultMarker(lat, lon, name, resultData) {
        console.log('🔧 addSearchResultMarker 호출됨:', { lat, lon, name });

        const coord = fromLonLat([lon, lat]);
        console.log('📍 변환된 좌표:', coord);

        // 기존 마커가 있는지 확인
        const existingMarker = this.searchResultMarkers.find(marker =>
            marker.lat === lat && marker.lon === lon
        );

        if (existingMarker) {
            console.log('⚠️ 이미 존재하는 마커:', existingMarker);
            // 이미 존재하는 마커라면 해당 위치로 이동만
            this.goToLocation(lat, lon);
            return;
        }

        // 새로운 마커 생성
        const marker = {
            id: Date.now().toString(),
            name: name,
            lat: lat,
            lon: lon,
            coord: coord,
            displayName: resultData.display_name,
            addedAt: new Date().toISOString(),
            type: 'search-result'
        };

        console.log('🆕 새 마커 객체 생성:', marker);

        // 마커 피처 생성
        const feature = new Feature({
            geometry: new Point(coord),
            properties: marker
        });

        // 검색 결과 마커 전용 스타일 적용
        feature.setStyle(this.getSearchResultMarkerStyle());

        // 벡터 레이어에 추가
        this.vectorSource.addFeature(feature);
        console.log('✅ 벡터 레이어에 피처 추가됨');

        // 마커 정보 저장
        this.searchResultMarkers.push(marker);
        this.searchResultFeatures.push(feature);
        console.log('💾 마커 정보 저장됨. 총 개수:', this.searchResultMarkers.length);

        // 검색 결과 목록에 추가
        this.addToSearchResultsList(marker);

        // 토스트 메시지 표시
        this.showToast(`📍 "${name}" 위치에 마커가 추가되었습니다.`, 'success');

        // 검색 결과 마커 패널로 스크롤 및 하이라이트
        this.highlightAndScrollToPanel('search-results-panel', '검색 결과 마커가 추가되었습니다!');

        console.log('✅ 검색 결과 마커 추가 완료:', marker);
    }

    // 검색 결과 마커 전용 스타일
    getSearchResultMarkerStyle() {
        return new Style({
            image: new Icon({
                anchor: [0.5, 1],
                src: 'data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="%23ff6b6b"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/></svg>'
            })
        });
    }

    // 즐겨찾기 마커 전용 스타일 (주황색)
    getFavoriteMarkerStyle() {
        return new Style({
            image: new Icon({
                anchor: [0.5, 1],
                src: 'data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="%23ff9500"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/></svg>'
            })
        });
    }

    // 검색 결과 목록에 추가
    addToSearchResultsList(marker) {
        console.log('📋 addToSearchResultsList 호출됨:', marker);

        const searchResultsList = document.getElementById('searchResultsList');
        if (!searchResultsList) {
            console.error('❌ 검색 결과 목록 요소를 찾을 수 없습니다.');
            return;
        }

        console.log('✅ searchResultsList 요소 찾음');

        // 기존 빈 메시지 제거
        const emptyElement = searchResultsList.querySelector('.empty');
        if (emptyElement) {
            emptyElement.remove();
            console.log('🗑️ 기존 빈 메시지 제거됨');
        }

        // 마커 항목 HTML 생성
        const markerItem = document.createElement('div');
        markerItem.className = 'search-result-marker-item';
        markerItem.dataset.id = marker.id;
        markerItem.innerHTML = `
            <div class="marker-info">
                <div class="marker-name">📍 ${marker.name}</div>
                <div class="marker-details">${marker.displayName.split(',').slice(1, 3).join(',')}</div>
                <div class="marker-time">${new Date(marker.addedAt).toLocaleString('ko-KR')}</div>
            </div>
            <div class="marker-actions">
                <button class="go-to-marker" title="해당 위치로 이동">🚀</button>
                <button class="remove-marker" title="마커 삭제">🗑️</button>
            </div>
        `;

        console.log('🆕 마커 항목 HTML 생성됨');

        // 이벤트 리스너 추가
        markerItem.querySelector('.go-to-marker').addEventListener('click', () => {
            console.log('🚀 이동 버튼 클릭됨:', marker.name);
            this.goToLocation(marker.lat, marker.lon);
        });

        markerItem.querySelector('.remove-marker').addEventListener('click', () => {
            console.log('🗑️ 삭제 버튼 클릭됨:', marker.name);
            this.removeSearchResultMarker(marker.id);
        });

        // 목록 맨 위에 추가
        searchResultsList.insertBefore(markerItem, searchResultsList.firstChild);
        console.log('✅ 마커 항목이 목록에 추가됨');
    }

    // 검색 결과 마커 삭제
    removeSearchResultMarker(markerId) {
        const markerIndex = this.searchResultMarkers.findIndex(m => m.id === markerId);
        if (markerIndex === -1) return;

        const marker = this.searchResultMarkers[markerIndex];
        const featureIndex = this.searchResultFeatures.findIndex(f =>
            f.get('properties').id === markerId
        );

        // 벡터 레이어에서 피처 제거
        if (featureIndex !== -1) {
            this.vectorSource.removeFeature(this.searchResultFeatures[featureIndex]);
            this.searchResultFeatures.splice(featureIndex, 1);
        }

        // 마커 정보 제거
        this.searchResultMarkers.splice(markerIndex, 1);

        // DOM에서 마커 항목 제거
        const markerItem = document.querySelector(`[data-id="${markerId}"]`);
        if (markerItem) {
            markerItem.remove();
        }

        // 토스트 메시지 표시
        this.showToast(`🗑️ "${marker.name}" 마커가 삭제되었습니다.`, 'info');

        console.log('🗑️ 검색 결과 마커 삭제:', marker.name);
    }



    // 모든 검색 결과 마커 삭제
    clearAllSearchResultMarkers() {
        // 벡터 레이어에서 모든 검색 결과 피처 제거
        this.searchResultFeatures.forEach(feature => {
            this.vectorSource.removeFeature(feature);
        });

        // 배열 초기화
        this.searchResultMarkers = [];
        this.searchResultFeatures = [];

        // DOM에서 모든 마커 항목 제거
        const searchResultsList = document.getElementById('searchResultsList');
        if (searchResultsList) {
            searchResultsList.innerHTML = '<div class="empty">검색 결과를 선택하면 여기에 마커가 추가됩니다.</div>';
        }

        // 토스트 메시지 표시
        this.showToast('🗑️ 모든 검색 결과 마커가 삭제되었습니다.', 'info');

        console.log('🗑️ 모든 검색 결과 마커 삭제 완료');
    }

    // 즐겨찾기 마커 삭제
    removeFavoriteMarker(markerId) {
        const markerIndex = this.favoriteMarkers.findIndex(m => m.id === markerId);
        if (markerIndex === -1) return;

        const marker = this.favoriteMarkers[markerIndex];
        const featureIndex = this.favoriteFeatures.findIndex(f =>
            f.get('properties').id === markerId
        );

        // 벡터 레이어에서 피처 제거
        if (featureIndex !== -1) {
            this.vectorSource.removeFeature(this.favoriteFeatures[featureIndex]);
            this.favoriteFeatures.splice(featureIndex, 1);
        }

        // 마커 정보 제거
        this.favoriteMarkers.splice(markerIndex, 1);

        // 토스트 메시지 표시
        this.showToast(`🗑️ 즐겨찾기 마커가 삭제되었습니다.`, 'info');

        console.log('🗑️ 즐겨찾기 마커 삭제:', marker);
    }

    // 모든 즐겨찾기 마커 삭제
    clearAllFavoriteMarkers() {
        // 벡터 레이어에서 모든 즐겨찾기 피처 제거
        this.favoriteFeatures.forEach(feature => {
            this.vectorSource.removeFeature(feature);
        });

        // 배열 초기화
        this.favoriteMarkers = [];
        this.favoriteFeatures = [];

        // 토스트 메시지 표시
        this.showToast('🗑️ 모든 즐겨찾기 마커가 삭제되었습니다.', 'info');

        console.log('🗑️ 모든 즐겨찾기 마커 삭제 완료');
    }

    // 외부 스크립트 동적 로더 (Promise 래핑)
    loadExternalScript(src) {
        return new Promise((resolve, reject) => {
            // 이미 로드된 스크립트가 있는지 확인
            const existing = document.querySelector(`script[src="${src}"]`);
            if (existing) {
                if (existing.getAttribute('data-loaded') === 'true') {
                    resolve();
                    return;
                }
                existing.addEventListener('load', () => resolve());
                existing.addEventListener('error', () => reject(new Error(`Failed to load script: ${src}`)));
                return;
            }

            const script = document.createElement('script');
            script.src = src;
            script.async = true;
            script.addEventListener('load', () => {
                script.setAttribute('data-loaded', 'true');
                resolve();
            });
            script.addEventListener('error', () => reject(new Error(`Failed to load script: ${src}`)));
            document.head.appendChild(script);
        });
    }

    async ensureExifLoaded() {
        if (this.aiLibs.exifLoaded && typeof EXIF !== 'undefined') return;
        this.showToast('📷 이미지 메타데이터 모듈 로드 중...', 'info');
        await this.loadExternalScript('https://cdn.jsdelivr.net/npm/exif-js@2.3.0/exif.js');
        this.aiLibs.exifLoaded = true;
    }

    async ensureTesseractLoaded() {
        if (this.aiLibs.tesseractLoaded && typeof Tesseract !== 'undefined') return;
        this.showToast('🧠 OCR 모듈 로드 중...', 'info');
        await this.loadExternalScript('https://cdn.jsdelivr.net/npm/tesseract.js@5.0.4/dist/tesseract.min.js');
        this.aiLibs.tesseractLoaded = true;
    }

    async ensureTensorFlowScriptsLoaded() {
        if (this.aiLibs.tfScriptsLoaded && typeof tf !== 'undefined' && typeof cocoSsd !== 'undefined' && typeof mobilenet !== 'undefined') {
            return;
        }
        this.showToast('🤖 AI 비전 모듈 로드 중...', 'info');
        await this.loadExternalScript('https://cdn.jsdelivr.net/npm/@tensorflow/tfjs@4.15.0/dist/tf.min.js');
        await this.loadExternalScript('https://cdn.jsdelivr.net/npm/@tensorflow-models/coco-ssd@2.2.3/dist/coco-ssd.min.js');
        await this.loadExternalScript('https://cdn.jsdelivr.net/npm/@tensorflow-models/mobilenet@2.1.1/dist/mobilenet.min.js');
        this.aiLibs.tfScriptsLoaded = true;
    }

    // 이미지 업로드 핸들러
    async handleImageUpload(event) {
        const file = event.target.files[0];
        if (!file) return;

        // 이미지 파일인지 확인
        if (!file.type.startsWith('image/')) {
            this.showToast('이미지 파일만 업로드할 수 있습니다.', 'error');
            return;
        }

        this.showToast('📷 이미지에서 위치 정보를 추출하는 중...', 'info');

        // EXIF 라이브러리 동적 로드
        try {
            await this.ensureExifLoaded();
        } catch (e) {
            console.error('❌ EXIF 라이브러리 로드 실패:', e);
            this.showToast('이미지 메타데이터 모듈을 불러오지 못했습니다. AI 분석만 시도합니다.', 'error');
            this.estimateLocationFromImage(file);
            return;
        }

        // EXIF 데이터 읽기
        EXIF.getData(file, () => {
            try {
                // GPS 좌표 추출
                const lat = EXIF.getTag(file, 'GPSLatitude');
                const latRef = EXIF.getTag(file, 'GPSLatitudeRef');
                const lon = EXIF.getTag(file, 'GPSLongitude');
                const lonRef = EXIF.getTag(file, 'GPSLongitudeRef');

                if (!lat || !lon) {
                    // GPS 정보가 없으면 AI 기반 위치 추정 시도
                    console.log('📍 GPS 정보 없음, AI 기반 위치 추정 시작');
                    this.estimateLocationFromImage(file);
                    return;
                }

                // GPS 좌표를 십진수로 변환
                const latitude = this.convertDMSToDD(lat, latRef);
                const longitude = this.convertDMSToDD(lon, lonRef);

                console.log('📍 추출된 GPS 좌표:', latitude, longitude);

                // 역 지오코딩 수행
                this.reverseGeocode(latitude, longitude, file.name);

            } catch (error) {
                console.error('❌ GPS 좌표 추출 오류:', error);
                this.showToast('이미지에서 위치 정보를 추출하는데 실패했습니다.', 'error');
                event.target.value = '';
            }
        });
    }

    // DMS (도/분/초)를 십진수로 변환
    convertDMSToDD(dms, ref) {
        let dd = dms[0] + dms[1] / 60 + dms[2] / (60 * 60);
        if (ref === 'S' || ref === 'W') {
            dd = dd * -1;
        }
        return dd;
    }

    // 역 지오코딩 (좌표 → 주소)
    async reverseGeocode(lat, lon, imageName, customName = null) {
        try {
            this.showToast('🔍 주소를 찾는 중...', 'info');

            const url = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lon}&zoom=18&addressdetails=1`;

            const response = await fetch(url, {
                method: 'GET',
                headers: {
                    'Accept': 'application/json',
                    'User-Agent': 'WebGIS-Application/1.0'
                }
            });

            if (!response.ok) {
                throw new Error(`역 지오코딩 실패: ${response.status}`);
            }

            const data = await response.json();
            console.log('📍 역 지오코딩 결과:', data);

            // 주소 정보 추출
            const address = data.address || {};
            const displayName = data.display_name || `${lat.toFixed(6)}, ${lon.toFixed(6)}`;

            // 주소 구성
            let addressParts = [];
            if (address.road) addressParts.push(address.road);
            if (address.house_number) addressParts.push(address.house_number);
            if (address.neighbourhood || address.suburb) addressParts.push(address.neighbourhood || address.suburb);
            if (address.city || address.town || address.village) addressParts.push(address.city || address.town || address.village);
            if (address.state) addressParts.push(address.state);
            if (address.country) addressParts.push(address.country);

            const formattedAddress = addressParts.length > 0
                ? addressParts.join(', ')
                : displayName;

            // 지도에 마커 추가 및 이동
            const coordinate = fromLonLat([lon, lat]);
            this.map.getView().animate({
                center: coordinate,
                zoom: 16,
                duration: 1000
            });

            // 마커 추가
            const markerFeature = new Feature({
                geometry: new Point(coordinate),
                name: `📷 ${imageName}`,
                address: formattedAddress,
                type: 'image-location'
            });

            markerFeature.setStyle(new Style({
                image: new Icon({
                    src: 'data:image/svg+xml;base64,' + btoa(`
                        <svg xmlns="http://www.w3.org/2000/svg" width="32" height="32" viewBox="0 0 24 24" fill="#ff6b6b">
                            <path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/>
                        </svg>
                    `),
                    scale: 1,
                    anchor: [0.5, 1]
                })
            }));

            this.vectorSource.addFeature(markerFeature);

            // 오버레이로 주소 표시
            const popup = document.createElement('div');
            popup.className = 'image-location-popup';
            const popupHeader = customName ? customName : `📷 ${imageName}`;
            popup.innerHTML = `
                <div class="popup-header">${popupHeader}</div>
                <div class="popup-address">${formattedAddress}</div>
                <div class="popup-coords">위도: ${lat.toFixed(6)}, 경도: ${lon.toFixed(6)}</div>
            `;

            const overlay = new Overlay({
                element: popup,
                positioning: 'bottom-center',
                stopEvent: false,
                offset: [0, -10]
            });

            this.map.addOverlay(overlay);
            overlay.setPosition(coordinate);

            // 5초 후 오버레이 자동 제거
            setTimeout(() => {
                this.map.removeOverlay(overlay);
            }, 5000);

            this.showToast(`✅ 위치를 찾았습니다: ${formattedAddress}`, 'success');

            // 파일 입력 초기화
            const imageUpload = document.getElementById('imageUpload');
            if (imageUpload) imageUpload.value = '';

        } catch (error) {
            console.error('❌ 역 지오코딩 오류:', error);
            this.showToast('주소를 찾는 중 오류가 발생했습니다.', 'error');
            const imageUpload = document.getElementById('imageUpload');
            if (imageUpload) imageUpload.value = '';
        }
    }

    // GeoSpy 스타일 분석 패널 표시
    showGeoSpyAnalysisPanel() {
        const panel = document.getElementById('geospyAnalysisPanel');
        if (panel) {
            panel.style.display = 'block';
            // 패널로 스크롤
            panel.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
        // 진행 상태 초기화
        this.resetGeoSpyProgress();
    }

    // GeoSpy 진행 상태 초기화
    resetGeoSpyProgress() {
        const steps = document.querySelectorAll('.geospy-step');
        steps.forEach(step => {
            step.classList.remove('active', 'completed', 'error');
            const icon = step.querySelector('.step-icon');
            if (icon) icon.textContent = '⏳';
        });
        this.updateGeoSpyProgress(0, '대기 중...');
    }

    // GeoSpy 진행 상태 업데이트
    updateGeoSpyProgress(percent, statusText) {
        const progressFill = document.getElementById('geospyProgressFill');
        const statusTextEl = document.querySelector('.geospy-status-text');

        if (progressFill) {
            progressFill.style.width = `${Math.min(100, Math.max(0, percent))}%`;
        }
        if (statusTextEl) {
            statusTextEl.textContent = statusText || '분석 중...';
        }
    }

    // GeoSpy 단계 업데이트
    updateGeoSpyStep(stepName, status) {
        const step = document.querySelector(`.geospy-step[data-step="${stepName}"]`);
        if (!step) return;

        step.classList.remove('active', 'completed', 'error');
        const icon = step.querySelector('.step-icon');

        if (status === 'active') {
            step.classList.add('active');
            if (icon) icon.textContent = '🔄';
        } else if (status === 'completed') {
            step.classList.add('completed');
            if (icon) icon.textContent = '✅';
        } else if (status === 'error') {
            step.classList.add('error');
            if (icon) icon.textContent = '❌';
        } else {
            if (icon) icon.textContent = '⏳';
        }
    }

    // GeoSpy 결과 표시
    showGeoSpyResults(locations, imageName = '이미지', langInfo = null) {
        const resultsSection = document.getElementById('geospyResultsSection');
        const resultsList = document.getElementById('geospyResultsList');
        const resultsCount = document.getElementById('geospyResultsCount');

        if (!resultsSection || !resultsList) return;

        if (locations && locations.length > 0) {
            resultsCount.textContent = `${locations.length}개 위치 발견`;
            resultsList.innerHTML = locations.map((loc, index) => `
                <div class="geospy-result-item" data-index="${index}">
                    <div class="geospy-result-header">
                        <span class="geospy-result-name">📍 ${loc.display_name?.split(',')[0] || '알 수 없음'}</span>
                        <span class="geospy-result-confidence">${Math.round((loc.confidence || 0.5) * 100)}%</span>
                    </div>
                    <div class="geospy-result-details">${loc.display_name || ''}</div>
                    <div class="geospy-result-meta">
                        <span class="geospy-result-source">${loc.source || 'AI'}</span>
                        ${langInfo && langInfo.languageName ? `<span class="geospy-result-lang">🌍 ${langInfo.languageName}</span>` : ''}
                    </div>
                </div>
            `).join('');

            // 결과 항목 클릭 이벤트 추가
            resultsList.querySelectorAll('.geospy-result-item').forEach((item, index) => {
                item.addEventListener('click', () => {
                    const location = locations[index];
                    if (location) {
                        this.displayLocationOnMap(location, imageName, langInfo);
                        this.showToast(`📍 ${location.display_name?.split(',')[0]} 위치로 이동했습니다.`, 'success');
                    }
                });
            });

            resultsSection.style.display = 'block';
        } else {
            resultsSection.style.display = 'none';
        }
    }

    // GPS 정보가 없을 때 이미지에서 위치 추정 (AI 기반) - GeoSpy 스타일
    async estimateLocationFromImage(file) {
        try {
            // GeoSpy 스타일 분석 패널 표시
            this.showGeoSpyAnalysisPanel();
            this.updateGeoSpyProgress(5, '이미지 분석 시작...');

            this.showToast('🤖 AI가 이미지를 분석하여 위치를 추정하는 중...', 'info');
            this.imageLocationEstimation.active = true;

            // AI 분석 방법 시도 (OCR, 이미지 특징 분석, 랜드마크 인식)
            this.updateGeoSpyStep('ocr', 'active');
            this.updateGeoSpyProgress(30, '텍스트 추출 중 (OCR)...');

            const ocrPromise = this.extractTextFromImage(file).then(result => {
                this.updateGeoSpyStep('ocr', 'completed');
                return result;
            });

            this.updateGeoSpyStep('vision', 'active');
            this.updateGeoSpyProgress(50, '이미지 특징 분석 중...');

            const featuresPromise = this.analyzeImageFeatures(file).then(result => {
                this.updateGeoSpyStep('vision', 'completed');
                return result;
            });

            this.updateGeoSpyStep('landmark', 'active');
            this.updateGeoSpyProgress(60, '랜드마크 인식 중...');

            const landmarkPromise = this.detectLandmarks(file).then(result => {
                this.updateGeoSpyStep('landmark', 'completed');
                return result;
            });

            const results = await Promise.allSettled([
                ocrPromise,
                featuresPromise,
                landmarkPromise
            ]);

            const locationCandidates = [];

            // OCR 결과 처리
            if (results[0].status === 'fulfilled' && results[0].value) {
                const textResults = results[0].value;
                if (textResults.length > 0) {
                    locationCandidates.push(...textResults);
                }
            }

            // 이미지 특징 분석 결과 처리
            if (results[1].status === 'fulfilled' && results[1].value) {
                const featureResults = results[1].value;
                if (featureResults.length > 0) {
                    locationCandidates.push(...featureResults);
                }
            }

            // 랜드마크 인식 결과 처리
            if (results[2].status === 'fulfilled' && results[2].value) {
                const landmarkResults = results[2].value;
                if (landmarkResults.length > 0) {
                    locationCandidates.push(...landmarkResults);
                }
            }

            if (locationCandidates.length === 0) {
                this.updateGeoSpyProgress(100, '위치 정보를 찾을 수 없습니다');
                this.updateGeoSpyStep('search', 'error');
                this.showToast('이미지에서 위치 정보를 찾을 수 없습니다. 더 명확한 랜드마크나 텍스트가 있는 사진을 시도해보세요.', 'error');
                const imageUpload = document.getElementById('imageUpload');
                if (imageUpload) imageUpload.value = '';
                setTimeout(() => this.hideGeoSpyAnalysisPanel(), 3000);
                return;
            }

            // 언어 정보를 후보에 포함
            // OCR 결과에서 텍스트 추출 시도
            let bestText = '';
            if (results[0].status === 'fulfilled' && results[0].value && results[0].value.length > 0) {
                bestText = results[0].value[0]?.query || '';
            }
            // 후보에서 텍스트 가져오기
            if (!bestText && locationCandidates.length > 0) {
                bestText = locationCandidates[0]?.query || '';
            }

            const langInfoForCandidates = locationCandidates.length > 0 ?
                (locationCandidates[0].langInfo || (bestText ? this.detectLanguageAndCountry(bestText) : null)) : null;

            // 각 후보에 언어 정보 추가
            locationCandidates.forEach(candidate => {
                if (!candidate.langInfo) {
                    candidate.langInfo = langInfoForCandidates;
                }
            });

            // 위치 검색 시작
            this.updateGeoSpyStep('search', 'active');
            this.updateGeoSpyProgress(70, '위치 검색 중...');

            // 가장 가능성 높은 위치 선택 및 표시
            await this.displayEstimatedLocations(locationCandidates, file.name);

        } catch (error) {
            console.error('❌ 위치 추정 오류:', error);
            this.updateGeoSpyProgress(100, '오류 발생');
            this.updateGeoSpyStep('search', 'error');
            this.showToast('위치 추정 중 오류가 발생했습니다.', 'error');
            const imageUpload = document.getElementById('imageUpload');
            if (imageUpload) imageUpload.value = '';
            setTimeout(() => this.hideGeoSpyAnalysisPanel(), 3000);
        } finally {
            this.imageLocationEstimation.active = false;
        }
    }

    // GeoSpy 분석 패널 숨기기
    hideGeoSpyAnalysisPanel() {
        const panel = document.getElementById('geospyAnalysisPanel');
        if (panel) {
            // 결과가 있으면 패널은 유지, 없으면 숨김
            const resultsSection = document.getElementById('geospyResultsSection');
            if (!resultsSection || resultsSection.style.display === 'none') {
                panel.style.display = 'none';
            }
        }
    }

    // TensorFlow.js 모델 로드
    async loadTensorFlowModels() {
        try {
            // TensorFlow 스크립트가 없으면 먼저 로드
            await this.ensureTensorFlowScriptsLoaded();

            if (typeof tf === 'undefined' || typeof cocoSsd === 'undefined' || typeof mobilenet === 'undefined') {
                console.warn('⚠️ TensorFlow.js 모델이 로드되지 않았습니다.');
                return;
            }

            this.showToast('🤖 AI 모델을 로드하는 중...', 'info');

            // COCO-SSD 모델 로드 (객체 인식)
            this.tfModels.cocoSSD = await cocoSsd.load();

            // MobileNet 모델 로드 (이미지 분류)
            this.tfModels.mobilenet = await mobilenet.load();

            this.tfModels.loaded = true;
            console.log('✅ TensorFlow.js 모델 로드 완료');
            this.showToast('✅ AI 모델 로드 완료', 'success');

        } catch (error) {
            console.error('❌ TensorFlow.js 모델 로드 오류:', error);
            this.tfModels.loaded = false;
        }
    }

    // OCR 텍스트 보정 함수
    correctOCRText(text) {
        if (!text || text.trim().length < 2) {
            return text;
        }

        let corrected = text;

        // 1. 공백 정리 (연속된 공백 제거, 줄바꿈 정리)
        corrected = corrected.replace(/\s+/g, ' ').trim();
        corrected = corrected.replace(/\n\s*\n/g, '\n');

        // 2. 일반적인 OCR 오류 수정
        const commonCorrections = {
            // 숫자와 문자 혼동
            '0': 'O', '1': 'I', '5': 'S', '8': 'B',
            // 한글 자음/모음 오류
            'ㅇ': '이', 'ㅈ': '지', 'ㅊ': '치',
            // 공백 오류
            '서울시': '서울 시', '부산시': '부산 시', '대구시': '대구 시',
            '인천시': '인천 시', '광주시': '광주 시', '대전시': '대전 시',
            '울산시': '울산 시', '제주시': '제주 시'
        };

        // 3. 특수문자 정리 (불필요한 특수문자 제거, 유용한 것은 유지)
        corrected = corrected.replace(/[^\w\s가-힣\-.,()]/g, ' ');

        // 4. 단어 경계 정리 (한글과 영문 사이 공백 추가)
        corrected = corrected.replace(/([가-힣])([A-Za-z])/g, '$1 $2');
        corrected = corrected.replace(/([A-Za-z])([가-힣])/g, '$1 $2');

        // 5. 숫자와 문자 사이 공백 정리
        corrected = corrected.replace(/(\d)([A-Za-z가-힣])/g, '$1 $2');
        corrected = corrected.replace(/([A-Za-z가-힣])(\d)/g, '$1 $2');

        // 6. 대소문자 정리 (장소 이름은 대문자로 시작)
        const lines = corrected.split('\n');
        corrected = lines.map(line => {
            const trimmed = line.trim();
            if (trimmed.length > 0 && /^[a-z]/.test(trimmed)) {
                // 첫 글자가 소문자면 대문자로 (영문인 경우만)
                if (/^[a-z]/.test(trimmed) && !/[가-힣]/.test(trimmed)) {
                    return trimmed.charAt(0).toUpperCase() + trimmed.slice(1);
                }
            }
            return trimmed;
        }).join('\n');

        // 7. 최종 공백 정리
        corrected = corrected.replace(/\s+/g, ' ').trim();

        console.log('✏️ 텍스트 보정 완료:', {
            원본길이: text.length,
            보정길이: corrected.length,
            변경사항: text !== corrected ? '있음' : '없음'
        });

        return corrected;
    }

    // 언어 감지 및 국가 매핑
    detectLanguageAndCountry(text) {
        if (!text || text.trim().length < 2) {
            return { language: null, countries: [], confidence: 0 };
        }

        // 언어별 국가 우선순위 매핑 (일본 제외)
        const languageCountryMap = {
            'kor': { countries: ['kr'], priority: 1.0, name: '한국어' },
            // 'jpn': { countries: ['jp'], priority: 1.0, name: '일본어' }, // 일본 제외
            'cmn': { countries: ['cn', 'tw', 'hk'], priority: 0.9, name: '중국어' },
            'fra': { countries: ['fr', 'be', 'ch', 'ca', 'lu', 'mc'], priority: 0.9, name: '프랑스어' },
            'deu': { countries: ['de', 'at', 'ch', 'li'], priority: 0.9, name: '독일어' },
            'spa': { countries: ['es', 'mx', 'ar', 'co', 'cl', 'pe'], priority: 0.9, name: '스페인어' },
            'ita': { countries: ['it', 'ch', 'sm', 'va'], priority: 0.9, name: '이탈리아어' },
            'eng': { countries: ['us', 'gb', 'ca', 'au', 'nz', 'ie'], priority: 0.7, name: '영어' },
            'por': { countries: ['pt', 'br', 'ao', 'mz'], priority: 0.9, name: '포르투갈어' },
            'rus': { countries: ['ru', 'by', 'kz', 'kg'], priority: 0.9, name: '러시아어' },
            'ara': { countries: ['sa', 'ae', 'eg', 'iq', 'jo', 'kw', 'lb', 'ma', 'om', 'qa', 'sy', 'tn', 'ye'], priority: 0.9, name: '아랍어' },
            'tha': { countries: ['th'], priority: 1.0, name: '태국어' },
            'vie': { countries: ['vn'], priority: 1.0, name: '베트남어' },
            'ind': { countries: ['id'], priority: 1.0, name: '인도네시아어' },
            'msa': { countries: ['my', 'sg', 'bn'], priority: 0.9, name: '말레이어' }
        };

        // 패턴 기반 언어 감지 (정확하고 빠른 감지)
        let detectedLang = null;

        // 한글 감지 (최우선순위 - 한글이 있으면 무조건 한국어)
        // 여러 한글 패턴으로 강력하게 감지
        const koreanPatterns = [
            /[가-힣]/,           // 기본 한글
            /[ㄱ-ㅎㅏ-ㅣ]/,      // 자음/모음
            /[가-힣]+[시도군구동리로길가]/,  // 한국 주소 패턴
            /서울|부산|대구|인천|광주|대전|울산|제주|경기|강원|충북|충남|전북|전남|경북|경남/  // 한국 도시명
        ];

        const hasKorean = koreanPatterns.some(pattern => pattern.test(text));
        const koreanCharCount = (text.match(/[가-힣]/g) || []).length;
        const totalCharCount = text.replace(/\s/g, '').length;
        const koreanRatio = totalCharCount > 0 ? koreanCharCount / totalCharCount : 0;

        console.log(`🔍 한글 감지 분석: 한글 문자 ${koreanCharCount}개, 전체 문자 ${totalCharCount}개, 비율 ${(koreanRatio * 100).toFixed(1)}%`);

        // 한글이 하나라도 있으면 무조건 한국어로 감지
        if (hasKorean || koreanCharCount > 0) {
            detectedLang = 'kor';
            console.log(`✅ 한국어로 강제 감지: 한글 문자 ${koreanCharCount}개 발견`);
        }
        // 일본어 감지 제외 (사용자 요청)
        // else if (/[ひらがな]/.test(text) || /[カタカナ]/.test(text)) {
        //     detectedLang = 'jpn';
        // } 
        // 중국어 감지 (한자만 있을 때)
        else if (/[一-龯]/.test(text)) {
            detectedLang = 'cmn';
        }
        // 프랑스어 감지 (특수 문자 + 프랑스어 단어)
        else if (/[àâäéèêëïîôùûüÿç]/.test(text) && /le|la|les|de|du|des|et|est|dans|pour|avec|sur|sous/.test(text.toLowerCase())) {
            detectedLang = 'fra';
        }
        // 독일어 감지 (움라우트 + 독일어 단어)
        else if (/[äöüß]/.test(text) && /der|die|das|und|ist|sind|von|zu|mit|auf/.test(text.toLowerCase())) {
            detectedLang = 'deu';
        }
        // 스페인어 감지 (악센트 + 스페인어 단어)
        else if (/[áéíóúñ]/.test(text) && /el|la|los|las|del|de|en|es|con|por/.test(text.toLowerCase())) {
            detectedLang = 'spa';
        }
        // 이탈리아어 감지 (악센트 + 이탈리아어 단어)
        else if (/[àèéìíîòóùú]/.test(text) && /il|la|gli|le|di|del|della|con|per|in/.test(text.toLowerCase())) {
            detectedLang = 'ita';
        }
        // 포르투갈어 감지 (악센트 + 포르투갈어 단어)
        else if (/[àáâãéêíóôõú]/.test(text) && /o|a|os|as|de|do|da|dos|das|em|no|na|com|por/.test(text.toLowerCase())) {
            detectedLang = 'por';
        }
        // 러시아어 감지 (키릴 문자)
        else if (/[а-яё]/.test(text)) {
            detectedLang = 'rus';
        }
        // 아랍어 감지 (아랍 문자)
        else if (/[ا-ي]/.test(text)) {
            detectedLang = 'ara';
        }
        // 기본값: 영어
        else {
            detectedLang = 'eng';
        }

        const langInfo = languageCountryMap[detectedLang] || languageCountryMap['eng'];

        console.log(`🌍 감지된 언어: ${langInfo.name} (${detectedLang}) → 가능한 국가: ${langInfo.countries.join(', ')}`);

        return {
            language: detectedLang,
            languageName: langInfo.name,
            countries: langInfo.countries,
            confidence: langInfo.priority
        };
    }

    // OCR로 이미지에서 텍스트 추출 (개선된 버전)
    async extractTextFromImage(file) {
        try {
            // Tesseract.js 동적 로드
            await this.ensureTesseractLoaded();

            this.showToast('📝 AI가 이미지에서 텍스트를 추출하는 중...', 'info');

            // 다중 언어로 텍스트 추출 시도 (정확도 향상)
            // 언어 우선순위: 한국어+영어, 한국어, 영어, 중국어, 프랑스어, 독일어, 스페인어, 이탈리아어 (일본어 제외)
            const languages = [
                { code: 'kor+eng', name: '한국어+영어', priority: 1.0 },
                { code: 'kor', name: '한국어', priority: 0.9 },
                { code: 'eng', name: '영어', priority: 0.8 },
                // { code: 'jpn', name: '일본어', priority: 0.9 }, // 일본어 제외
                { code: 'chi_sim', name: '중국어', priority: 0.9 },
                { code: 'fra', name: '프랑스어', priority: 0.9 },
                { code: 'deu', name: '독일어', priority: 0.9 },
                { code: 'spa', name: '스페인어', priority: 0.9 },
                { code: 'ita', name: '이탈리아어', priority: 0.9 }
            ];

            let bestText = '';
            let bestConfidence = 0;
            let bestLanguage = 'kor+eng';

            // 여러 언어로 시도하여 가장 좋은 결과 선택
            // 병렬로 여러 언어 시도 (성능 향상)
            const recognitionPromises = languages.slice(0, 5).map(async (lang) => {
                try {
                    const { data } = await Tesseract.recognize(file, lang.code, {
                        logger: m => {
                            if (m.status === 'recognizing text') {
                                // 진행 상태는 조용히 처리
                            }
                        }
                    });

                    return {
                        text: data.text || '',
                        confidence: data.confidence || 0,
                        language: lang.code,
                        languageName: lang.name,
                        priority: lang.priority
                    };
                } catch (e) {
                    console.warn(`언어 ${lang.code} 인식 실패:`, e);
                    return null;
                }
            });

            const results = await Promise.allSettled(recognitionPromises);

            // 가장 좋은 결과 선택 (한글 비율 우선 고려)
            for (const result of results) {
                if (result.status === 'fulfilled' && result.value) {
                    const r = result.value;

                    // 한글 문자 개수 확인
                    const koreanCount = (r.text.match(/[가-힣]/g) || []).length;
                    const koreanRatio = r.text.length > 0 ? koreanCount / r.text.length : 0;

                    // 한글이 있으면 점수에 큰 가중치 부여
                    let score = (r.text.length * 0.2) + (r.confidence * 0.3) + (r.priority * 0.1);
                    if (koreanCount > 0) {
                        score += koreanRatio * 2.0; // 한글 비율에 큰 가중치
                        score += Math.min(koreanCount / 10, 0.5); // 한글 개수 보너스
                        console.log(`🇰🇷 한국어 후보: ${r.languageName} - 한글 ${koreanCount}개, 점수: ${score.toFixed(2)}`);
                    } else {
                        console.log(`📝 일반 후보: ${r.languageName} - 점수: ${score.toFixed(2)}`);
                    }

                    const currentScore = (bestText.length * 0.2) + (bestConfidence * 0.3);
                    const currentKoreanCount = (bestText.match(/[가-힣]/g) || []).length;
                    const currentKoreanRatio = bestText.length > 0 ? currentKoreanCount / bestText.length : 0;
                    const currentKoreanBonus = currentKoreanCount > 0 ? (currentKoreanRatio * 2.0 + Math.min(currentKoreanCount / 10, 0.5)) : 0;
                    const currentTotalScore = currentScore + currentKoreanBonus;

                    if (score > currentTotalScore && r.text.trim().length >= 2) {
                        bestText = r.text;
                        bestConfidence = r.confidence;
                        bestLanguage = r.language;
                        console.log(`✅ 최적 언어 선택: ${r.languageName} (${r.language}) - 점수: ${score.toFixed(2)}`);
                    }
                }
            }

            // 기본 언어로 한 번 더 시도 (결과가 없을 때만)
            if (!bestText || bestText.trim().length < 2) {
                console.log('🔄 기본 언어(kor+eng)로 재시도...');
                const { data: { text } } = await Tesseract.recognize(file, 'kor+eng', {
                    logger: m => {
                        if (m.status === 'recognizing text') {
                            // 진행 상태는 조용히 처리
                        }
                    }
                });
                bestText = text;
                bestLanguage = 'kor+eng';
            }

            if (!bestText || bestText.trim().length < 2) {
                console.warn('⚠️ 텍스트 추출 실패 또는 텍스트 없음');
                return [];
            }

            console.log('📝 원본 추출된 텍스트:', bestText);
            console.log('📊 텍스트 인식 신뢰도:', bestConfidence);

            // 1단계: 텍스트 보정 (OCR 오류 수정)
            const correctedText = this.correctOCRText(bestText);
            console.log('✏️ 보정된 텍스트:', correctedText);

            // 2단계: 언어 감지 및 국가 추정 (보정된 텍스트로)
            const langInfo = this.detectLanguageAndCountry(correctedText);
            console.log('🌍 언어 감지 결과:', langInfo);
            console.log('📝 추출된 텍스트 샘플:', bestText.substring(0, 100));

            // 언어 감지 검증 및 강제 수정
            const koreanCount = (bestText.match(/[가-힣]/g) || []).length;
            const hiraganaCount = (bestText.match(/[ひらがな]/g) || []).length;
            const katakanaCount = (bestText.match(/[カタカナ]/g) || []).length;

            // 한글이 있으면 무조건 한국어로 강제 설정
            if (koreanCount > 0) {
                if (langInfo.language !== 'kor') {
                    console.warn(`⚠️ 한글 ${koreanCount}개가 있는데 ${langInfo.languageName}로 감지되었습니다. 한국어로 강제 변경합니다.`);
                    langInfo.language = 'kor';
                    langInfo.languageName = '한국어';
                    langInfo.countries = ['kr'];
                    langInfo.confidence = 1.0;
                }
                console.log(`✅ 한국어 감지 확인: 한글 문자 ${koreanCount}개 발견`);
            }

            // 일본어 감지 제외 (사용자 요청)
            // 히라가나/가타카나가 감지되면 로그만 출력하고 무시
            if (hiraganaCount > 0 || katakanaCount > 0) {
                console.log(`⚠️ 히라가나/가타카나 감지: 히라가나 ${hiraganaCount}개, 가타카나 ${katakanaCount}개 (일본어는 제외됨)`);
            }

            // 최종 언어 확인 로그
            console.log(`🎯 최종 언어 결정: ${langInfo.languageName} (${langInfo.language})`);
            console.log(`📍 검색 국가: ${langInfo.countries.join(', ')}`);

            // 텍스트에서 장소 이름 추출 (보정된 텍스트 사용)
            const lines = correctedText.split('\n').filter(line => line.trim().length > 1);
            const locationCandidates = [];

            // 언어 기반 국가 정보는 검색 쿼리로 사용하지 않음 (필터링에만 사용)
            // 언어 이름으로 검색하면 부정확한 결과가 나올 수 있음

            // 개선된 텍스트 분석 - 더 엄격한 필터링
            for (const line of lines) {
                const trimmed = line.trim();

                // 한글이 포함된 줄이나 영문 대문자로 시작하는 줄을 장소 후보로 간주
                if (trimmed.match(/[가-힣]/) || (trimmed.match(/^[A-Z]/) && trimmed.length > 2)) {
                    // 특수문자 제거 및 정리
                    let cleaned = trimmed.replace(/[^\w\s가-힣\-]/g, '').trim();

                    // 검색에 부적합한 텍스트 제외
                    const excludePatterns = [
                        /^\d+$/,  // 숫자만
                        /^[A-Z]{1,2}$/,  // 1-2자 영문 대문자만
                        /^(the|a|an|is|are|was|were|be|been|being|have|has|had|do|does|did|will|would|should|could|may|might|can|must)$/i,  // 일반 영어 단어
                        /^(이|그|저|이것|그것|저것|여기|거기|저기)$/,  // 한국어 지시어
                        /^(시|도|군|구|동|리|로|길|가)$/,  // 주소 단위만
                    ];

                    // 너무 짧거나 긴 텍스트 제외, 그리고 제외 패턴 확인
                    if (cleaned.length >= 3 && cleaned.length <= 40 &&
                        !excludePatterns.some(pattern => pattern.test(cleaned))) {
                        // 장소 이름 패턴 확인
                        const isLocationName = this.isLocationName(cleaned);
                        // 장소 이름이 아니면 신뢰도 낮춤
                        const confidence = isLocationName ? 0.85 : 0.3;

                        locationCandidates.push({
                            type: 'text',
                            query: cleaned,
                            confidence: confidence,
                            source: isLocationName ? 'AI OCR' : 'OCR',
                            countries: langInfo.countries, // 언어 기반 국가 힌트
                            language: langInfo.language,
                            langInfo: langInfo // 전체 언어 정보 포함
                        });
                    }
                }
            }

            // 단어 단위로도 분석 (보정된 텍스트 사용)
            const allWords = correctedText.split(/\s+/).filter(word => {
                const w = word.replace(/[^\w가-힣]/g, '');
                return w.length >= 2 && (w.match(/[가-힣]/) || w.match(/^[A-Z]/));
            });

            for (const word of allWords.slice(0, 10)) {
                const cleaned = word.replace(/[^\w가-힣]/g, '');
                if (cleaned.length >= 2 && this.isLocationName(cleaned)) {
                    locationCandidates.push({
                        type: 'text',
                        query: cleaned,
                        confidence: 0.7,
                        source: 'AI OCR (키워드)',
                        countries: langInfo.countries,
                        language: langInfo.language,
                        langInfo: langInfo // 전체 언어 정보 포함
                    });
                }
            }

            // TensorFlow.js로 객체 인식하여 추가 정보 추출
            if (this.tfModels.loaded) {
                const aiResults = await this.analyzeImageWithTensorFlow(file);
                if (aiResults.length > 0) {
                    locationCandidates.push(...aiResults);
                }
            }

            return locationCandidates.slice(0, 8); // 상위 8개만 반환

        } catch (error) {
            console.error('❌ OCR 오류:', error);
            return [];
        }
    }

    // TensorFlow.js로 이미지 분석
    async analyzeImageWithTensorFlow(file) {
        try {
            // 필요 시에만 TensorFlow 모델 로드
            if (!this.tfModels.loaded) {
                await this.loadTensorFlowModels();
                if (!this.tfModels.loaded) {
                    return [];
                }
            }

            this.showToast('🤖 AI가 이미지를 분석하는 중...', 'info');

            const image = await this.loadImageAsBase64(file);
            const img = await this.createImageElement(image);

            // 이미지를 TensorFlow 형식으로 변환
            const tensor = tf.browser.fromPixels(img);
            const resized = tf.image.resizeBilinear(tensor, [224, 224]);
            const normalized = resized.div(255.0);
            const batched = normalized.expandDims(0);

            const locationCandidates = [];

            // COCO-SSD로 객체 인식
            try {
                const predictions = await this.tfModels.cocoSSD.detect(img);
                console.log('🔍 COCO-SSD 인식 결과:', predictions);

                for (const prediction of predictions) {
                    const className = prediction.class;
                    const score = prediction.score;

                    // 장소와 관련된 객체만 필터링
                    const placeObjects = [
                        'building', 'tower', 'bridge', 'church', 'temple',
                        'monument', 'statue', 'fountain', 'clock', 'sign'
                    ];

                    if (placeObjects.includes(className.toLowerCase()) && score > 0.5) {
                        locationCandidates.push({
                            type: 'object',
                            query: className,
                            confidence: score * 0.7,
                            source: 'TensorFlow Object Detection'
                        });
                    }
                }
            } catch (error) {
                console.warn('COCO-SSD 인식 오류:', error);
            }

            // MobileNet으로 이미지 분류
            try {
                const predictions = await this.tfModels.mobilenet.classify(img);
                console.log('🔍 MobileNet 분류 결과:', predictions);

                for (const prediction of predictions.slice(0, 3)) {
                    const className = prediction.className.toLowerCase();
                    const probability = prediction.probability;

                    // 장소와 관련된 카테고리 필터링
                    const placeCategories = [
                        'building', 'tower', 'palace', 'temple', 'church',
                        'monument', 'landmark', 'bridge', 'park', 'plaza',
                        'street', 'road', 'avenue', 'station', 'airport'
                    ];

                    if (placeCategories.some(cat => className.includes(cat)) && probability > 0.3) {
                        locationCandidates.push({
                            type: 'category',
                            query: prediction.className,
                            confidence: probability * 0.6,
                            source: 'TensorFlow Image Classification'
                        });
                    }
                }
            } catch (error) {
                console.warn('MobileNet 분류 오류:', error);
            }

            // 텐서 정리
            tensor.dispose();
            resized.dispose();
            normalized.dispose();
            batched.dispose();

            return locationCandidates;

        } catch (error) {
            console.error('❌ TensorFlow 분석 오류:', error);
            return [];
        }
    }

    // 텍스트가 장소 이름인지 판단하는 함수 (개선된 버전)
    isLocationName(text) {
        if (!text || text.length < 2) return false;

        // 장소 이름 패턴
        const locationPatterns = [
            /^[가-힣]+(시|도|군|구|동|리|로|길|가|면|읍)$/,  // 한국 주소
            /^[A-Z][a-z]+ (Street|Avenue|Road|Park|Tower|Building|Palace|Temple|Church|Bridge|Station|Airport)$/i,  // 영문 주소
            /^[가-힣]+(궁|사|원|관|타워|빌딩|센터|공원|광장|다리|역|공항|박물관|미술관|성|문)$/,  // 한국 랜드마크
            /서울|부산|대구|인천|광주|대전|울산|제주|경기|강원|충북|충남|전북|전남|경북|경남|수원|성남|고양|용인|부천|안산|안양|평택|시흥|김포|의정부|광명|파주|이천|오산|구리|안성|포천|의왕|하남|양주|구리|남양주|화성|가평|양평|여주|이천/i,  // 도시명
            /^[가-힣]{2,10}$/,  // 2-10자 한글 (일반적인 장소명 길이)
            /^[A-Z][a-z]+$/,  // 영문 대문자로 시작하는 단어
            /\d+번지|\d+호/,  // 번지, 호수
        ];

        // 패턴 매칭
        if (locationPatterns.some(pattern => pattern.test(text))) {
            return true;
        }

        // 일반적인 장소 키워드 포함 여부
        const locationKeywords = [
            '타워', '빌딩', '센터', '공원', '광장', '다리', '역', '공항',
            '궁', '사', '원', '관', '성', '문', '박물관', '미술관',
            'Tower', 'Building', 'Center', 'Park', 'Square', 'Bridge',
            'Station', 'Airport', 'Palace', 'Temple', 'Church', 'Museum'
        ];

        return locationKeywords.some(keyword => text.includes(keyword));
    }

    // 이미지 특징 분석 (건물, 풍경 등)
    async analyzeImageFeatures(file) {
        try {
            // 기본 이미지 분석: 색상, 구성 등을 기반으로 간단한 특징 추출
            const image = await this.loadImageAsBase64(file);
            const img = await this.createImageElement(image);

            const features = [];

            // 이미지에서 건물, 하늘, 자연 등의 비율을 분석
            const analysis = await this.analyzeImageComposition(img);

            // 분석 결과를 바탕으로 장소 유형 추정
            if (analysis.hasBuildings) {
                features.push({
                    type: 'visual',
                    query: '도시 건물',
                    confidence: 0.5,
                    source: 'Visual Analysis'
                });
            }

            if (analysis.hasNature) {
                features.push({
                    type: 'visual',
                    query: '자연 풍경',
                    confidence: 0.4,
                    source: 'Visual Analysis'
                });
            }

            return features;

        } catch (error) {
            console.error('❌ 이미지 특징 분석 오류:', error);
            return [];
        }
    }


    // 이미지 요소 생성
    createImageElement(src) {
        return new Promise((resolve, reject) => {
            const img = new Image();
            img.onload = () => resolve(img);
            img.onerror = reject;
            img.src = src;
        });
    }

    // 이미지 구성 분석 (건물, 자연 등)
    async analyzeImageComposition(img) {
        return new Promise((resolve) => {
            const canvas = document.createElement('canvas');
            const ctx = canvas.getContext('2d');
            canvas.width = Math.min(img.width, 200);
            canvas.height = Math.min(img.height, 200);

            ctx.drawImage(img, 0, 0, canvas.width, canvas.height);

            const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
            const data = imageData.data;

            let hasBuildings = false;
            let hasNature = false;
            let skyPixels = 0;
            let greenPixels = 0;

            // 간단한 색상 분석
            for (let i = 0; i < data.length; i += 4) {
                const r = data[i];
                const g = data[i + 1];
                const b = data[i + 2];

                // 하늘 색상 (파란색 계열)
                if (b > r && b > g && b > 150) {
                    skyPixels++;
                }

                // 자연 색상 (녹색 계열)
                if (g > r && g > b && g > 100) {
                    greenPixels++;
                }
            }

            const skyRatio = skyPixels / (data.length / 4);
            const greenRatio = greenPixels / (data.length / 4);

            // 하늘이 적고 다양한 색상이면 건물 가능성
            hasBuildings = skyRatio < 0.3 && greenRatio < 0.3;
            // 녹색이 많으면 자연 풍경
            hasNature = greenRatio > 0.2;

            resolve({ hasBuildings, hasNature, skyRatio, greenRatio });
        });
    }

    // 랜드마크 인식
    async detectLandmarks(file) {
        try {
            // 기본 키워드 기반 랜드마크 인식
            // 여기서는 OCR로 추출한 텍스트에서 랜드마크 키워드를 찾는 방식 사용

            const textResults = await this.extractTextFromImage(file);
            const landmarkKeywords = [
                '타워', 'Tower', '빌딩', 'Building', '센터', 'Center',
                '궁', 'Palace', '사원', 'Temple', '교회', 'Church', '성당', 'Cathedral',
                '공원', 'Park', '광장', 'Square', '다리', 'Bridge', '역', 'Station',
                '공항', 'Airport', '호텔', 'Hotel', '박물관', 'Museum', '미술관', 'Gallery',
                '서울', 'Seoul', '부산', 'Busan', '제주', 'Jeju', '경복궁', 'Gyeongbokgung',
                '남산', 'Namsan', '한강', 'Han River', '롯데타워', 'Lotte Tower'
            ];

            const landmarks = [];
            for (const result of textResults) {
                for (const keyword of landmarkKeywords) {
                    if (result.query.includes(keyword)) {
                        landmarks.push({
                            type: 'landmark',
                            query: result.query,
                            confidence: 0.9,
                            source: 'Landmark Detection'
                        });
                        break;
                    }
                }
            }

            return landmarks;

        } catch (error) {
            console.error('❌ 랜드마크 인식 오류:', error);
            return [];
        }
    }

    // 이미지를 Base64로 로드
    loadImageAsBase64(file) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onload = () => resolve(reader.result);
            reader.onerror = reject;
            reader.readAsDataURL(file);
        });
    }

    // 추정된 위치들을 검색하고 표시
    async displayEstimatedLocations(candidates, imageName) {
        try {
            console.log('🔍 위치 후보:', candidates);
            this.showToast(`🔍 ${candidates.length}개 후보를 검색하는 중...`, 'info');

            // 언어 정보 추출 (첫 번째 후보에서)
            let langInfo = null;
            if (candidates.length > 0) {
                // langInfo가 직접 있으면 사용
                if (candidates[0].langInfo) {
                    langInfo = candidates[0].langInfo;
                }
                // countries와 language가 있으면 langInfo 재구성
                else if (candidates[0].countries && candidates[0].language) {
                    const languageCountryMap = {
                        'kor': { countries: ['kr'], priority: 1.0, name: '한국어' },
                        'cmn': { countries: ['cn', 'tw', 'hk'], priority: 0.9, name: '중국어' },
                        'fra': { countries: ['fr', 'be', 'ch', 'ca', 'lu', 'mc'], priority: 0.9, name: '프랑스어' },
                        'deu': { countries: ['de', 'at', 'ch', 'li'], priority: 0.9, name: '독일어' },
                        'spa': { countries: ['es', 'mx', 'ar', 'co', 'cl', 'pe'], priority: 0.9, name: '스페인어' },
                        'ita': { countries: ['it', 'ch', 'sm', 'va'], priority: 0.9, name: '이탈리아어' },
                        'eng': { countries: ['us', 'gb', 'ca', 'au', 'nz', 'ie'], priority: 0.7, name: '영어' },
                        'por': { countries: ['pt', 'br', 'ao', 'mz'], priority: 0.9, name: '포르투갈어' },
                        'rus': { countries: ['ru', 'by', 'kz', 'kg'], priority: 0.9, name: '러시아어' },
                        'ara': { countries: ['sa', 'ae', 'eg', 'iq', 'jo', 'kw', 'lb', 'ma', 'om', 'qa', 'sy', 'tn', 'ye'], priority: 0.9, name: '아랍어' },
                        'tha': { countries: ['th'], priority: 1.0, name: '태국어' },
                        'vie': { countries: ['vn'], priority: 1.0, name: '베트남어' },
                        'ind': { countries: ['id'], priority: 1.0, name: '인도네시아어' },
                        'msa': { countries: ['my', 'sg', 'bn'], priority: 0.9, name: '말레이어' }
                    };
                    const langData = languageCountryMap[candidates[0].language] || languageCountryMap['eng'];
                    langInfo = {
                        language: candidates[0].language,
                        languageName: langData.name,
                        countries: candidates[0].countries || langData.countries,
                        confidence: langData.priority
                    };
                }
            }

            if (langInfo) {
                console.log(`🌍 검색 언어: ${langInfo.languageName} → 국가: ${langInfo.countries.join(', ')}`);
            }

            // 중복 제거 및 정렬 (confidence 기준)
            const uniqueCandidates = [];
            const seen = new Set();

            for (const candidate of candidates.sort((a, b) => (b.confidence || 0) - (a.confidence || 0))) {
                const key = candidate.query.toLowerCase().trim();
                if (key && key.length >= 2 && !seen.has(key)) {
                    seen.add(key);
                    uniqueCandidates.push(candidate);
                }
            }

            console.log('✅ 중복 제거 후 후보:', uniqueCandidates);

            if (uniqueCandidates.length === 0) {
                this.showToast('검색할 후보가 없습니다. 이미지에서 더 많은 정보를 추출해보세요.', 'error');
                const imageUpload = document.getElementById('imageUpload');
                if (imageUpload) imageUpload.value = '';
                return;
            }

            // 상위 5개 후보 검색 (언어 기반 국가 필터링 적용)
            const searchPromises = uniqueCandidates.slice(0, 5).map(candidate => {
                console.log(`🔍 검색 시도: "${candidate.query}"`, candidate.countries ? `(국가: ${candidate.countries.join(',')})` : '');
                return this.performSearchForLocation(candidate.query, candidate).then(results => {
                    console.log(`✅ "${candidate.query}" 검색 결과:`, results?.length || 0, '개');
                    return {
                        candidate,
                        results: results || []
                    };
                }).catch(error => {
                    console.error(`❌ "${candidate.query}" 검색 오류:`, error);
                    return { candidate, results: [] };
                });
            });

            const searchResults = await Promise.all(searchPromises);

            // 검색 결과가 있는 후보들 수집 (정확도 기반 필터링)
            const validLocations = [];
            for (const { candidate, results } of searchResults) {
                if (results && results.length > 0) {
                    console.log(`✅ "${candidate.query}"에서 ${results.length}개 위치 발견`);
                    for (const result of results.slice(0, 2)) { // 각 후보당 최대 2개 결과
                        // 검색 결과의 정확도 확인
                        const resultName = result.display_name || '';
                        const queryLower = candidate.query.toLowerCase();
                        const resultLower = resultName.toLowerCase();

                        // 검색 쿼리가 결과 이름에 포함되어 있는지 확인
                        const queryInResult = resultLower.includes(queryLower) ||
                            queryLower.split(/\s+/).some(word =>
                                word.length >= 3 && resultLower.includes(word)
                            );

                        // 정확도 점수 계산
                        let accuracyScore = candidate.confidence || 0.5;
                        if (queryInResult) {
                            accuracyScore += 0.2; // 쿼리가 결과에 포함되면 보너스
                        }

                        validLocations.push({
                            ...result,
                            confidence: Math.min(accuracyScore, 1.0), // 최대 1.0
                            source: candidate.source || 'AI',
                            originalQuery: candidate.query,
                            accuracyScore: accuracyScore
                        });
                    }
                } else {
                    console.log(`⚠️ "${candidate.query}" 검색 결과 없음`);
                }
            }

            // 정확도 점수로 정렬 (높은 점수 우선)
            validLocations.sort((a, b) => (b.accuracyScore || b.confidence) - (a.accuracyScore || a.confidence));

            console.log('📍 최종 유효한 위치:', validLocations.length, '개');

            // 검색 결과 추천 시스템 (언어 기반)
            // langInfo가 없으면 null로 전달 (안전하게 처리)
            const recommendedLocations = this.recommendLocations(validLocations, langInfo || null);
            console.log('🎯 추천된 위치:', recommendedLocations.length, '개');

            if (validLocations.length === 0) {
                // 더 넓은 검색 시도
                console.log('🔄 넓은 범위 검색 시도...');
                const broadSearchResults = await this.performBroadSearch(uniqueCandidates);
                if (broadSearchResults.length > 0) {
                    validLocations.push(...broadSearchResults);
                }
            }

            if (validLocations.length === 0) {
                console.error('❌ 모든 검색 시도 실패');
                this.showToast('위치를 찾을 수 없습니다. 텍스트나 랜드마크가 명확한 사진을 사용해보세요.', 'error');
                const imageUpload = document.getElementById('imageUpload');
                if (imageUpload) imageUpload.value = '';
                return;
            }

            // 추천된 위치가 있으면 우선 사용, 없으면 전체 결과 사용
            const locationsToShow = recommendedLocations.length > 0 ? recommendedLocations : validLocations;

            // langInfo가 없으면 null로 설정 (안전하게 처리)
            const safeLangInfo = langInfo || null;

            // GeoSpy 결과 표시
            this.updateGeoSpyStep('search', 'completed');
            this.updateGeoSpyProgress(100, `✅ ${locationsToShow.length}개 위치 발견`);
            this.showGeoSpyResults(locationsToShow, imageName, safeLangInfo);

            // 여러 후보가 있으면 사용자에게 선택하게 하기
            if (locationsToShow.length > 1) {
                this.showLocationCandidates(locationsToShow, imageName, safeLangInfo);
            } else if (locationsToShow.length === 1) {
                // 하나만 있으면 바로 표시
                this.displayLocationOnMap(locationsToShow[0], imageName, safeLangInfo);
            } else {
                // 추천 결과가 없으면 전체 결과 표시
                if (validLocations.length > 1) {
                    this.showLocationCandidates(validLocations, imageName, safeLangInfo);
                } else if (validLocations.length === 1) {
                    this.displayLocationOnMap(validLocations[0], imageName, safeLangInfo);
                }
            }

        } catch (error) {
            console.error('❌ 위치 표시 오류:', error);
            this.showToast('위치를 표시하는 중 오류가 발생했습니다.', 'error');
            const imageUpload = document.getElementById('imageUpload');
            if (imageUpload) imageUpload.value = '';
        }
    }

    // 검색 결과 추천 시스템
    recommendLocations(locations, langInfo) {
        if (!locations || locations.length === 0) {
            return [];
        }

        const recommendations = [];

        for (const location of locations) {
            let recommendationScore = location.accuracyScore || location.confidence || 0.5;

            // 1. 언어 기반 국가 일치 확인
            if (langInfo && langInfo.countries && langInfo.countries.length > 0) {
                const locationCountry = location.address?.country_code ||
                    location.address?.country ||
                    this.extractCountryFromAddress(location.display_name);

                if (locationCountry && langInfo.countries.includes(locationCountry.toLowerCase())) {
                    recommendationScore += 0.3; // 국가 일치 보너스
                    console.log(`✅ 국가 일치: ${locationCountry} (${langInfo.languageName})`);
                }
            }

            // 2. 정확도 점수 확인
            if (location.accuracyScore && location.accuracyScore > 0.7) {
                recommendationScore += 0.2; // 높은 정확도 보너스
            }

            // 3. 주소 완성도 확인
            const addressParts = (location.display_name || '').split(',').length;
            if (addressParts >= 3) {
                recommendationScore += 0.1; // 상세한 주소 보너스
            }

            recommendations.push({
                ...location,
                recommendationScore: recommendationScore
            });
        }

        // 추천 점수로 정렬
        recommendations.sort((a, b) => b.recommendationScore - a.recommendationScore);

        // 상위 3개만 반환
        return recommendations.slice(0, 3);
    }

    // 주소에서 국가 코드 추출
    extractCountryFromAddress(address) {
        if (!address) return null;

        // 주소의 마지막 부분이 보통 국가명
        const parts = address.split(',').map(p => p.trim());
        const lastPart = parts[parts.length - 1]?.toLowerCase();

        // 국가 코드 매핑
        const countryMap = {
            'korea': 'kr', 'south korea': 'kr', '대한민국': 'kr', '한국': 'kr',
            'china': 'cn', '중국': 'cn',
            'france': 'fr', '프랑스': 'fr',
            'germany': 'de', '독일': 'de',
            'spain': 'es', '스페인': 'es',
            'italy': 'it', '이탈리아': 'it',
            'united states': 'us', 'usa': 'us', '미국': 'us',
            'united kingdom': 'gb', 'uk': 'gb', '영국': 'gb'
        };

        for (const [key, code] of Object.entries(countryMap)) {
            if (lastPart.includes(key)) {
                return code;
            }
        }

        return null;
    }

    // 여러 위치 후보를 사용자에게 보여주기
    showLocationCandidates(locations, imageName, langInfo = null) {
        // 검색 결과 패널에 후보 표시
        const searchResults = document.getElementById('searchResults');
        if (!searchResults) return;

        const candidatesHTML = `
            <div class="results-header">🤖 AI 위치 추정 결과 (${locations.length}개 후보)</div>
            ${locations.map((loc, index) => `
                <div class="search-result-item ai-candidate" data-index="${index}" style="cursor: pointer;">
                    <div class="search-result-name">📍 ${loc.display_name.split(',')[0]}</div>
                    <div class="search-result-details">${loc.display_name.split(',').slice(1, 3).join(',')}</div>
                    <div class="ai-confidence" style="font-size: 11px; color: #9333ea; margin-top: 4px;">신뢰도: ${Math.round((loc.confidence || 0.5) * 100)}% (${loc.source})</div>
                </div>
            `).join('')}
        `;

        searchResults.innerHTML = candidatesHTML;
        searchResults.classList.add('show');

        // langInfo를 클로저로 저장 (안전하게 처리)
        const safeLangInfo = langInfo || null;

        // 후보 클릭 이벤트
        searchResults.querySelectorAll('.ai-candidate').forEach((item, index) => {
            item.addEventListener('click', () => {
                this.displayLocationOnMap(locations[index], imageName, safeLangInfo);
                searchResults.classList.remove('show');
            });
        });
    }

    // 지도에 위치 표시
    displayLocationOnMap(location, imageName, langInfo = null) {
        const lat = parseFloat(location.lat);
        const lon = parseFloat(location.lon);
        const coordinate = fromLonLat([lon, lat]);

        this.map.getView().animate({
            center: coordinate,
            zoom: 15,
            duration: 1000
        });

        // 마커 추가
        const markerFeature = new Feature({
            geometry: new Point(coordinate),
            name: `🤖 ${imageName} (AI 추정)`,
            address: location.display_name,
            type: 'ai-estimated-location',
            confidence: location.confidence,
            source: location.source
        });

        markerFeature.setStyle(new Style({
            image: new Icon({
                src: 'data:image/svg+xml;base64,' + btoa(`
                    <svg xmlns="http://www.w3.org/2000/svg" width="32" height="32" viewBox="0 0 24 24" fill="#9333ea">
                        <path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/>
                        <circle cx="12" cy="9" r="1.5" fill="white"/>
                    </svg>
                `),
                scale: 1,
                anchor: [0.5, 1]
            })
        }));

        this.vectorSource.addFeature(markerFeature);

        // 오버레이로 정보 표시
        const popup = document.createElement('div');
        popup.className = 'image-location-popup ai-location-popup';
        const confidencePercent = Math.round((location.confidence || 0.5) * 100);
        const recommendationScore = location.recommendationScore ? Math.round(location.recommendationScore * 100) : null;
        // langInfo 안전하게 처리
        const safeLangInfo = langInfo || null;
        const langInfoText = safeLangInfo && safeLangInfo.languageName ? `🌍 감지된 언어: ${safeLangInfo.languageName}` : '';

        popup.innerHTML = `
            <div class="popup-header">🤖 ${imageName} (AI 추정)</div>
            ${langInfoText ? `<div class="popup-language">${langInfoText}</div>` : ''}
            <div class="popup-address">${location.display_name}</div>
            <div class="popup-coords">위도: ${lat.toFixed(6)}, 경도: ${lon.toFixed(6)}</div>
            <div class="popup-confidence">신뢰도: ${confidencePercent}% (${location.source})</div>
            ${recommendationScore ? `<div class="popup-recommendation">⭐ 추천 점수: ${recommendationScore}%</div>` : ''}
            <div class="popup-hint">💡 AI가 이미지를 분석하여 추정한 위치입니다.</div>
        `;

        const overlay = new Overlay({
            element: popup,
            positioning: 'bottom-center',
            stopEvent: false,
            offset: [0, -10]
        });

        this.map.addOverlay(overlay);
        overlay.setPosition(coordinate);

        // 8초 후 오버레이 자동 제거
        setTimeout(() => {
            this.map.removeOverlay(overlay);
        }, 8000);

        this.showToast(`✅ 위치를 찾았습니다: ${location.display_name.split(',')[0]}`, 'success');

        // 파일 입력 초기화
        const imageUpload = document.getElementById('imageUpload');
        if (imageUpload) imageUpload.value = '';
    }

    // 위치 검색을 위한 별도 함수 (언어 기반 국가 필터링 포함)
    async performSearchForLocation(query, candidate = null) {
        try {
            if (!query || query.trim().length < 2) {
                return [];
            }

            const cleanQuery = query.trim();

            // 언어 기반 국가 코드 필터링
            let countryCodes = '';
            if (candidate && candidate.countries && candidate.countries.length > 0) {
                countryCodes = candidate.countries.join(',');
                console.log(`🌍 국가 필터 적용: ${countryCodes} (언어: ${candidate.language || candidate.languageName || 'unknown'})`);
            }

            // 국가 코드가 있으면 우선 검색, 없으면 전역 검색
            let url = `https://nominatim.openstreetmap.org/search?format=json&q=${encodeURIComponent(cleanQuery)}&limit=5&addressdetails=1`;
            if (countryCodes) {
                url += `&countrycodes=${countryCodes}`;
            }

            const response = await fetch(url, {
                method: 'GET',
                headers: {
                    'Accept': 'application/json',
                    'User-Agent': 'WebGIS-Application/1.0'
                }
            });

            if (!response.ok) {
                console.error(`❌ 검색 API 오류: ${response.status}`);
                // 국가 필터가 있으면 필터 없이 재시도
                if (countryCodes) {
                    console.log('🔄 국가 필터 없이 재검색 시도...');
                    return await this.performSearchForLocation(cleanQuery, null);
                }
                return [];
            }

            const data = await response.json();

            // 국가 필터 결과가 없고 필터가 적용되었으면 전역 검색
            if ((!data || data.length === 0) && countryCodes) {
                console.log('🔄 국가 필터 결과 없음, 전역 검색 시도...');
                const globalResults = await this.performSearchForLocation(cleanQuery, null);
                return globalResults;
            }

            return data || [];

        } catch (error) {
            console.error('❌ 위치 검색 오류:', error);
            return [];
        }
    }

    // 더 넓은 범위로 검색 시도
    async performBroadSearch(candidates) {
        try {
            const validLocations = [];

            // 각 후보의 키워드 추출 및 조합 검색
            for (const candidate of candidates.slice(0, 3)) {
                const query = candidate.query;

                // 키워드 분리 및 부분 검색
                const words = query.split(/\s+/).filter(w => w.length >= 2);

                for (const word of words.slice(0, 2)) {
                    const results = await this.performSearchForLocation(word);
                    if (results.length > 0) {
                        for (const result of results.slice(0, 1)) {
                            validLocations.push({
                                ...result,
                                confidence: (candidate.confidence || 0.5) * 0.7,
                                source: `${candidate.source} (부분 검색)`,
                                originalQuery: word
                            });
                        }
                    }
                }
            }

            return validLocations;
        } catch (error) {
            console.error('❌ 넓은 범위 검색 오류:', error);
            return [];
        }
    }

    // 이미지 탐색 토글
    toggleImageSearch() {
        this.imageSearchActive = !this.imageSearchActive;
        const panel = document.getElementById('imageSearchPanel');
        const btn = document.getElementById('imageSearchBtn');

        if (this.imageSearchActive) {
            if (panel) {
                panel.style.display = 'block';
                // 패널로 부드럽게 스크롤
                setTimeout(() => {
                    panel.scrollIntoView({
                        behavior: 'smooth',
                        block: 'start',
                        inline: 'nearest'
                    });
                }, 100);
            }
            if (btn) {
                btn.classList.add('active');
                btn.style.background = 'linear-gradient(135deg, #00f2fe 0%, #4facfe 100%)';
            }
            this.showToast('🖼️ 이미지 탐색 모드가 활성화되었습니다. 지도를 클릭하세요.', 'info');
        } else {
            if (panel) panel.style.display = 'none';
            if (btn) {
                btn.classList.remove('active');
                btn.style.background = '';
            }
            this.showToast('이미지 탐색 모드가 비활성화되었습니다.', 'info');
            this.showToast('이미지 탐색 모드가 비활성화되었습니다.', 'info');

            // 마커 제거
            if (this.imageSearchMarkerFeature) {
                this.vectorSource.removeFeature(this.imageSearchMarkerFeature);
                this.imageSearchMarkerFeature = null;
            }
        }
    }

    // 이미지 탐색용 마커 추가
    addImageSearchMarker(coordinate) {
        // 기존 마커 제거
        if (this.imageSearchMarkerFeature) {
            this.vectorSource.removeFeature(this.imageSearchMarkerFeature);
        }

        const marker = new Feature({
            geometry: new Point(coordinate)
        });

        marker.setStyle(new Style({
            image: new Icon({
                anchor: [0.5, 1],
                src: 'https://cdn-icons-png.flaticon.com/512/1042/1042339.png', // 카메라 아이콘
                scale: 0.07,
                color: '#4facfe' // 파란색 틴트
            })
        }));

        this.vectorSource.addFeature(marker);
        this.imageSearchMarkerFeature = marker;
    }
    async searchImagesAtLocation(lat, lon) {
        console.log('🖼️ 이미지 검색 시작:', lat, lon);

        const loadingEl = document.getElementById('imageSearchLoading');
        const galleryEl = document.getElementById('imageGallery');
        const emptyEl = document.getElementById('imageSearchEmpty');
        const infoEl = document.getElementById('imageSearchInfo');
        const gridEl = document.getElementById('imageGrid');
        const countEl = document.getElementById('galleryCount');
        const titleEl = document.getElementById('galleryTitle');
        const newsAlert = document.getElementById('newsAlert');

        // UI 초기화
        if (newsAlert) newsAlert.style.display = 'none';
        if (infoEl) infoEl.style.display = 'none';
        if (galleryEl) galleryEl.style.display = 'none';
        if (emptyEl) emptyEl.style.display = 'none';
        if (loadingEl) loadingEl.style.display = 'block';
        if (gridEl) gridEl.innerHTML = '';

        this.currentImageSearchLocation = { lat, lon };
        this.latestNewsItems = []; // 소식 초기화

        let images = [];

        try {
            // 먼저 위치 이름 가져오기
            const locationName = await this.getLocationName(lat, lon);
            console.log('📍 위치 이름:', locationName);

            // 방법 1: Wikimedia Commons 지오서치 (위치 기반)
            const wikiImages = await this.searchWikimediaImages(lat, lon);
            if (wikiImages.length > 0) {
                images = wikiImages;
                console.log(`✅ Wikimedia에서 ${images.length}개 이미지 발견`);
            }

            // 방법 2: 위치 이름 기반 검색
            if (images.length === 0 && locationName) {
                const locationKeywords = this.extractLocationKeywords(locationName);
                console.log('🔑 위치 키워드:', locationKeywords);

                for (const keyword of locationKeywords.slice(0, 2)) {
                    const keywordImages = await this.searchUnsplashImages(keyword);
                    if (keywordImages.length > 0) {
                        images.push(...keywordImages);
                        console.log(`✅ "${keyword}"로 ${keywordImages.length}개 이미지 발견`);
                        break;
                    }
                }
            }

            // 방법 3: 더 넓은 반경으로 Wikimedia 재시도
            if (images.length === 0) {
                const wideWikiImages = await this.searchWikimediaImages(lat, lon, 10000);
                if (wideWikiImages.length > 0) {
                    images = wideWikiImages;
                    console.log(`✅ 넓은 범위에서 ${images.length}개 이미지 발견`);
                }
            }

            if (loadingEl) loadingEl.style.display = 'none';

            if (images.length > 0) {
                console.log(`✅ ${images.length}개 이미지 발견`);
                this.displayImageGallery(images, lat, lon);
            } else {
                console.log('⚠️ 이미지를 찾을 수 없음');
                if (emptyEl) emptyEl.style.display = 'block';
                this.showToast('이 위치에서 이미지를 찾을 수 없습니다. 다른 위치를 시도해보세요.', 'info');
            }

            // 위치 소식도 함께 검색
            this.searchLocationNews(lat, lon);

        } catch (error) {
            console.error('❌ 이미지 검색 오류:', error);
            if (loadingEl) loadingEl.style.display = 'none';
            if (emptyEl) emptyEl.style.display = 'block';
            this.showToast('이미지 검색 중 오류가 발생했습니다.', 'error');
        }
    }

    // 위치 이름에서 키워드 추출
    extractLocationKeywords(locationName) {
        if (!locationName) return [];

        // 주소를 쉼표로 분리하고 주요 키워드 추출
        const parts = locationName.split(',').map(p => p.trim()).filter(p => p.length > 0);
        const keywords = [];

        // 첫 번째 부분 (가장 구체적인 위치)
        if (parts.length > 0) {
            keywords.push(parts[0]);
        }

        // 두 번째 부분 (도시/지역)
        if (parts.length > 1) {
            keywords.push(parts[1]);
        }

        // 국가명 제거하고 주요 키워드만
        const filtered = keywords.filter(k => {
            const lower = k.toLowerCase();
            return !lower.includes('south korea') &&
                !lower.includes('republic of korea') &&
                !lower.includes('대한민국') &&
                k.length > 2;
        });

        return filtered.length > 0 ? filtered : [locationName];
    }

    // 위치 이름 기반 이미지 검색 (무료 서비스 사용 - Wikimedia 기반 텍스트 검색)
    async searchUnsplashImages(query) {
        try {
            // Wikimedia 텍스트 검색을 여러 키워드로 시도
            const images = [];
            const searchTerms = [
                `${query} street`,
                `${query} road`,
                `${query} city`,
                `${query} downtown`,
                `${query} night street`,
                `${query} avenue`
            ];

            for (let i = 0; i < searchTerms.length; i++) {
                const searchTerm = searchTerms[i];
                const imageUrl = await this.getImageUrlForLocation(searchTerm, i);
                if (imageUrl) {
                    images.push({
                        url: imageUrl,
                        fullUrl: imageUrl,
                        title: query,
                        description: `${query}의 거리/도시 이미지`,
                        lat: this.currentImageSearchLocation?.lat || 0,
                        lon: this.currentImageSearchLocation?.lon || 0,
                        distance: 0
                    });
                }
            }

            return images;

        } catch (error) {
            console.error('이미지 검색 오류:', error);
            return [];
        }
    }

    // 위치에 대한 이미지 URL 가져오기
    async getImageUrlForLocation(query, index) {
        try {
            // Wikimedia Commons에서 검색어로 이미지 찾기
            const url = `https://commons.wikimedia.org/w/api.php?` +
                `action=query&` +
                `list=search&` +
                `srsearch=${encodeURIComponent(query)}&` +
                `srnamespace=6&` + // 파일 네임스페이스
                `srlimit=1&` +
                `format=json&` +
                `origin=*`;

            const response = await fetch(url);
            if (!response.ok) return null;

            const data = await response.json();
            if (data.query && data.query.search && data.query.search.length > 0) {
                const pageId = data.query.search[0].pageid;
                const imageUrl = `https://commons.wikimedia.org/w/api.php?` +
                    `action=query&` +
                    `pageids=${pageId}&` +
                    `prop=imageinfo&` +
                    `iiprop=url|thumburl&` +
                    `iiurlwidth=400&` +
                    `format=json&` +
                    `origin=*`;

                const imgResponse = await fetch(imageUrl);
                if (imgResponse.ok) {
                    const imgData = await imgResponse.json();
                    if (imgData.query && imgData.query.pages && imgData.query.pages[pageId]) {
                        const page = imgData.query.pages[pageId];
                        if (page.imageinfo && page.imageinfo.length > 0) {
                            return page.imageinfo[0].thumburl || page.imageinfo[0].url;
                        }
                    }
                }
            }

            return null;
        } catch (error) {
            console.error('이미지 URL 가져오기 오류:', error);
            return null;
        }
    }

    // Backend API를 통해 거리/위치 이미지 검색 (CORS 문제 없이 서버에서 처리)
    async searchWikimediaImages(lat, lon, radius = 5000) {
        try {
            const params = new URLSearchParams({
                lat: String(lat),
                lon: String(lon)
            });
            const response = await fetch(`http://localhost:3000/api/street-images?${params.toString()}`);
            if (!response.ok) {
                console.error('Street Images API 오류:', response.status);
                return [];
            }
            const data = await response.json();
            return Array.isArray(data) ? data : [];
        } catch (error) {
            console.error('Street Images API 호출 오류:', error);
            return [];
        }
    }

    // 위치 이름 기반 일반 이미지 검색 (대체 방법)
    async searchLocationImages(locationName) {
        try {
            // 간단한 이미지 검색 서비스 사용
            // 또는 Unsplash를 다시 시도
            return await this.searchUnsplashImages(locationName);
        } catch (error) {
            console.error('위치 이미지 검색 오류:', error);
            return [];
        }
    }


    // 이미지 갤러리 표시
    displayImageGallery(images, lat, lon) {
        const galleryEl = document.getElementById('imageGallery');
        const gridEl = document.getElementById('imageGrid');
        const countEl = document.getElementById('galleryCount');
        const titleEl = document.getElementById('galleryTitle');

        if (!galleryEl || !gridEl) return;

        // 역 지오코딩으로 위치 이름 가져오기
        this.getLocationName(lat, lon).then(locationName => {
            if (titleEl) {
                titleEl.textContent = locationName || `위도: ${lat.toFixed(4)}, 경도: ${lon.toFixed(4)}`;
            }
        });

        if (countEl) countEl.textContent = `${images.length}개`;

        gridEl.innerHTML = images.map((img, index) => {
            // 제목 길이 제한
            const shortTitle = img.title.length > 30 ? img.title.substring(0, 30) + '...' : img.title;
            return `
            <div class="image-item" data-index="${index}">
                <img src="${img.url}" alt="${shortTitle}" loading="lazy" 
                     onerror="this.src='data:image/svg+xml,%3Csvg xmlns=\\'http://www.w3.org/2000/svg\\' width=\\'400\\' height=\\'300\\'%3E%3Crect fill=\\'%23f3f4f6\\' width=\\'400\\' height=\\'300\\'/%3E%3Ctext x=\\'50%25\\' y=\\'50%25\\' text-anchor=\\'middle\\' fill=\\'%2394a3b8\\' font-size=\\'14\\'%3E이미지 로드 실패%3C/text%3E%3C/svg%3E';">
                <div class="image-item-overlay">
                    <div class="image-item-title" title="${img.title}">${shortTitle}</div>
                    ${img.distance ? `<div class="image-item-distance">📍 ${img.distance.toFixed(0)}m</div>` : ''}
                </div>
            </div>
        `;
        }).join('');

        // 이미지 클릭 이벤트
        gridEl.querySelectorAll('.image-item').forEach((item, index) => {
            item.addEventListener('click', () => {
                this.showImageViewer(images[index], item);
            });
        });

        galleryEl.style.display = 'block';

        // 이미지가 로드되면 패널 위치로 자동 스크롤하여 결과 노출
        const panel = document.getElementById('imageSearchPanel');
        if (panel) {
            setTimeout(() => {
                panel.scrollIntoView({ behavior: 'smooth', block: 'start' });
                // 시각적 강조
                panel.classList.add('panel-highlight');
                setTimeout(() => panel.classList.remove('panel-highlight'), 1500);
            }, 100);
        }
    }

    // 위치 이름 가져오기 (역 지오코딩)
    async getLocationName(lat, lon) {
        try {
            const url = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lon}&zoom=10`;
            const response = await fetch(url, {
                headers: {
                    'User-Agent': 'WebGIS-Application/1.0'
                }
            });
            if (response.ok) {
                const data = await response.json();
                return data.display_name || '';
            }
        } catch (error) {
            console.error('위치 이름 가져오기 오류:', error);
        }
        return '';
    }

    // 이미지 뷰어 표시
    showImageViewer(image, triggerElement = null) {
        this.lastImageViewerTrigger = triggerElement; // 닫을 때 돌아갈 위치 저장
        const modal = document.getElementById('imageViewerModal');
        const img = document.getElementById('imageViewerImg');
        const info = document.getElementById('imageViewerInfo');

        if (!modal || !img) return;

        img.src = image.fullUrl || image.url;
        img.alt = image.title;

        if (info) {
            info.innerHTML = `
                <div class="viewer-title">${image.title}</div>
                ${image.description ? `<div class="viewer-description">${image.description}</div>` : ''}
                <div class="viewer-location">위도: ${image.lat.toFixed(6)}, 경도: ${image.lon.toFixed(6)}</div>
            `;
        }

        // 관련 소식 표시
        const newsContainer = document.getElementById('viewerNewsContainer');
        const newsList = document.getElementById('viewerNewsList');

        if (newsContainer && newsList) {
            if (this.latestNewsItems && this.latestNewsItems.length > 0) {
                newsContainer.style.display = 'block';
                newsList.innerHTML = this.latestNewsItems.map(item => `
                    <div class="news-item" onclick="window.open('${item.url}', '_blank')">
                        <div class="news-item-header">
                            <span class="news-item-source">${item.source}</span>
                            <span class="news-item-date">${item.date}</span>
                        </div>
                        <h5 class="news-item-title">${item.title}</h5>
                        <p class="news-item-description">${item.description}</p>
                    </div>
                `).join('');
            } else {
                newsContainer.style.display = 'none';
            }
        }

        modal.style.display = 'flex';

        // 사진을 클릭하면 위로 올라가는 효과 (window, sidebar, grid 모두 초기화)
        // 모달이 즉시 뜨므로, 배경 스크롤을 즉시 잠그고 위치를 초기화함
        window.scrollTo(0, 0);
        document.body.style.overflow = 'hidden';

        const sidebar = document.querySelector('.sidebar');
        if (sidebar) sidebar.scrollTop = 0;

        const imageGrid = document.getElementById('imageGrid');
        if (imageGrid) imageGrid.scrollTop = 0;
    }

    // 이미지 뷰어 닫기
    closeImageViewer() {
        const modal = document.getElementById('imageViewerModal');
        if (modal) {
            modal.style.display = 'none';
            modal.style.display = 'none';
            document.body.style.overflow = '';

            // 닫을 때 원래 보던 위치로 자동 스크롤
            if (this.lastImageViewerTrigger) {
                setTimeout(() => {
                    this.lastImageViewerTrigger.scrollIntoView({ behavior: 'smooth', block: 'center' });
                    this.lastImageViewerTrigger = null;
                }, 50);
            }
        }
    }

    // 위치 주변 소식 검색
    async searchLocationNews(lat, lon) {
        const newsSection = document.getElementById('locationNewsSection');
        const newsLoading = document.getElementById('newsLoading');
        const newsList = document.getElementById('newsList');
        const newsEmpty = document.getElementById('newsEmpty');
        const newsCount = document.getElementById('newsCount');

        if (!newsSection) return;

        // 소식 섹션 표시
        newsSection.style.display = 'block';
        if (newsLoading) newsLoading.style.display = 'block';
        if (newsList) newsList.innerHTML = '';
        if (newsEmpty) newsEmpty.style.display = 'none';

        try {
            // 위치 이름 가져오기
            const locationName = await this.getLocationName(lat, lon);
            if (!locationName) {
                if (newsLoading) newsLoading.style.display = 'none';
                if (newsEmpty) newsEmpty.style.display = 'block';
                return;
            }

            console.log('📰 위치 소식 검색:', locationName);

            // 위치 키워드 추출
            const keywords = this.extractLocationKeywords(locationName);
            const searchQuery = keywords[0] || locationName.split(',')[0];

            // 여러 소스에서 뉴스 검색 (뉴스 기사 우선)
            const newsItems = [];

            // 방법 1: 실제 뉴스 기사 검색 (최우선)
            const koreanQuery = locationName.split(',')[0].trim(); // 첫 번째 부분 (가장 구체적인 위치명)
            console.log('📰 뉴스 검색어:', koreanQuery);

            // 한국어 뉴스 검색
            const koreanNews = await this.searchNewsArticles(koreanQuery, 'ko');
            if (koreanNews.length > 0) {
                newsItems.push(...koreanNews);
                console.log(`✅ 한국어 뉴스 ${koreanNews.length}개 발견`);
            }

            // 영어 뉴스 검색 (한국어 결과가 적을 때)
            if (newsItems.length < 3) {
                const englishNews = await this.searchNewsArticles(searchQuery, 'en');
                if (englishNews.length > 0) {
                    newsItems.push(...englishNews);
                    console.log(`✅ 영어 뉴스 ${englishNews.length}개 발견`);
                }
            }

            // 방법 2: 네이버 뉴스 검색 (한국어 우선)
            if (newsItems.length < 10) {
                const naverNews = await this.searchNaverNews(koreanQuery);
                if (naverNews.length > 0) {
                    newsItems.push(...naverNews);
                    console.log(`✅ 네이버 뉴스 ${naverNews.length}개 발견`);
                }
            }

            // 방법 3: 다음 뉴스 검색
            if (newsItems.length < 10) {
                const daumNews = await this.searchDaumNews(koreanQuery);
                if (daumNews.length > 0) {
                    newsItems.push(...daumNews);
                    console.log(`✅ 다음 뉴스 ${daumNews.length}개 발견`);
                }
            }

            // 방법 4: Wikipedia 검색 (1개만, 뉴스가 부족할 때)
            if (newsItems.length < 5) {
                const wikiNews = await this.searchWikipediaNews(koreanQuery, true); // 한국어 우선
                if (wikiNews.length > 0) {
                    newsItems.push(wikiNews[0]); // 1개만 추가
                } else if (newsItems.length < 3) {
                    const englishWikiNews = await this.searchWikipediaNews(searchQuery, false);
                    if (englishWikiNews.length > 0) {
                        newsItems.push(englishWikiNews[0]); // 1개만 추가
                    }
                }
            }

            // 방법 3: 위치 기반 일반 정보 (뉴스와 Wikipedia가 모두 없을 때만)
            if (newsItems.length === 0) {
                const locationInfo = await this.getLocationInfo(locationName, lat, lon);
                if (locationInfo) {
                    newsItems.push(locationInfo);
                }
            }

            if (newsLoading) newsLoading.style.display = 'none';

            if (newsItems.length > 0) {
                this.latestNewsItems = newsItems; // 뷰어용으로 저장
                this.displayNewsList(newsItems, locationName);
                if (newsCount) newsCount.textContent = `${newsItems.length}개`;

                // 뉴스 알림 표시 (네비게이션 중이 아닐 때만)
                const newsAlert = document.getElementById('newsAlert');
                const newsAlertText = document.getElementById('newsAlertText');
                const newsAlertBtn = document.getElementById('newsAlertBtn');

                if (newsAlert && !this.isNavigating) {
                    newsAlert.style.display = 'flex';
                    if (newsAlertText) newsAlertText.textContent = `위치 소식 ${newsItems.length}개가 있습니다.`;

                    if (newsAlertBtn) {
                        newsAlertBtn.onclick = () => {
                            const newsSection = document.getElementById('locationNewsSection');
                            if (newsSection) {
                                newsSection.scrollIntoView({ behavior: 'smooth', block: 'start' });
                                newsSection.classList.add('panel-highlight');
                                setTimeout(() => newsSection.classList.remove('panel-highlight'), 2000);
                            }
                        };
                    }
                }
            } else {
                if (newsEmpty) newsEmpty.style.display = 'block';
                if (newsCount) newsCount.textContent = '0개';
            }

        } catch (error) {
            console.error('❌ 소식 검색 오류:', error);
            if (newsLoading) newsLoading.style.display = 'none';
            if (newsEmpty) newsEmpty.style.display = 'block';
        }
    }

    // 실제 뉴스 기사 검색
    async searchNewsArticles(query, lang = 'ko') {
        try {
            const newsItems = [];

            // 방법 1: Google News RSS 검색
            const googleNews = await this.searchGoogleNewsRSS(query, lang);
            if (googleNews.length > 0) {
                newsItems.push(...googleNews);
            }

            // 방법 2: Wikipedia 최근 변경사항 (뉴스성 있는 정보)
            if (newsItems.length < 5) {
                const wikiRecent = await this.searchWikipediaRecentChanges(query, lang);
                if (wikiRecent.length > 0) {
                    newsItems.push(...wikiRecent);
                }
            }

            return newsItems;
        } catch (error) {
            console.error('뉴스 기사 검색 오류:', error);
            return [];
        }
    }

    // Google News RSS 검색
    async searchGoogleNewsRSS(query, lang = 'ko') {
        try {
            // RSS2JSON 서비스를 통해 Google News RSS 파싱
            const countryCode = lang === 'ko' ? 'KR' : 'US';
            const languageCode = lang === 'ko' ? 'ko' : 'en';
            const rssUrl = `https://news.google.com/rss/search?q=${encodeURIComponent(query)}&hl=${languageCode}&gl=${countryCode}&ceid=${countryCode}:${languageCode}`;

            // RSS2JSON API 사용 (무료, CORS 지원)
            const proxyUrl = `https://api.rss2json.com/v1/api.json?rss_url=${encodeURIComponent(rssUrl)}&api_key=public&count=10`;

            const response = await fetch(proxyUrl);
            if (!response.ok) {
                console.log('RSS2JSON API 실패, 다른 방법 시도');
                return [];
            }

            const data = await response.json();
            const newsItems = [];

            if (data.status === 'ok' && data.items && data.items.length > 0) {
                for (const item of data.items.slice(0, 10)) {
                    // 제목에서 출처 제거 (Google News 형식: "제목 - 출처")
                    const titleMatch = item.title.match(/^(.+?)\s*-\s*(.+)$/);
                    const cleanTitle = titleMatch ? titleMatch[1].trim() : item.title;
                    const source = titleMatch ? titleMatch[2].trim() : 'Google News';

                    newsItems.push({
                        title: cleanTitle,
                        description: item.content || item.description || '',
                        url: item.link,
                        source: `📰 ${source}`,
                        date: item.pubDate ? new Date(item.pubDate).toLocaleDateString('ko-KR') : new Date().toLocaleDateString('ko-KR'),
                        type: 'news',
                        language: lang,
                        isNews: true
                    });
                }
            }

            if (newsItems.length > 0) {
                console.log(`✅ Google News에서 ${newsItems.length}개 뉴스 기사 발견`);
            }

            return newsItems;
        } catch (error) {
            console.error('Google News RSS 검색 오류:', error);
            return [];
        }
    }

    // Wikipedia 최근 변경사항 검색 (뉴스성 있는 정보)
    async searchWikipediaRecentChanges(query, lang = 'ko') {
        try {
            const baseUrl = lang === 'ko' ? 'https://ko.wikipedia.org' : 'https://en.wikipedia.org';

            // Wikipedia에서 최근 변경된 페이지 검색
            const searchUrl = `${baseUrl}/w/api.php?` +
                `action=query&` +
                `list=search&` +
                `srsearch=${encodeURIComponent(query)}&` +
                `srlimit=10&` +
                `format=json&` +
                `origin=*`;

            const response = await fetch(searchUrl);
            if (!response.ok) return [];

            const data = await response.json();
            const newsItems = [];

            if (data.query && data.query.search && data.query.search.length > 0) {
                // 최근 변경사항이 있는 페이지 우선 선택
                for (const item of data.query.search.slice(0, 5)) {
                    // 페이지 정보 가져오기
                    const pageUrl = `${baseUrl}/w/api.php?` +
                        `action=query&` +
                        `pageids=${item.pageid}&` +
                        `prop=extracts|info|revisions&` +
                        `exintro=true&` +
                        `exchars=150&` +
                        `rvprop=timestamp&` +
                        `rvlimit=1&` +
                        `inprop=url&` +
                        `format=json&` +
                        `origin=*`;

                    const pageResponse = await fetch(pageUrl);
                    if (pageResponse.ok) {
                        const pageData = await pageResponse.json();
                        if (pageData.query && pageData.query.pages && pageData.query.pages[item.pageid]) {
                            const page = pageData.query.pages[item.pageid];
                            const revisions = page.revisions || [];
                            const lastModified = revisions.length > 0 ? revisions[0].timestamp : null;

                            // 최근 1년 이내 수정된 페이지만 뉴스로 간주
                            const isRecent = lastModified ?
                                (Date.now() - new Date(lastModified).getTime()) < (365 * 24 * 60 * 60 * 1000) : true;

                            if (isRecent) {
                                const sourceName = lang === 'ko' ? '📰 뉴스 (Wikipedia)' : '📰 News (Wikipedia)';

                                newsItems.push({
                                    title: item.title,
                                    description: page.extract || item.snippet,
                                    url: `${baseUrl}/wiki/${encodeURIComponent(item.title.replace(/ /g, '_'))}`,
                                    source: sourceName,
                                    date: lastModified ? new Date(lastModified).toLocaleDateString('ko-KR') : new Date().toLocaleDateString('ko-KR'),
                                    type: 'news',
                                    language: lang,
                                    isNews: true
                                });
                            }
                        }
                    }
                }
            }

            return newsItems;
        } catch (error) {
            console.error('Wikipedia 최근 변경사항 검색 오류:', error);
            return [];
        }
    }

    // 네이버 뉴스 검색
    async searchNaverNews(query) {
        try {
            // 네이버 뉴스 RSS 피드 사용
            // 네이버 뉴스 검색 RSS: https://news.naver.com/main/rss/search.naver?query={query}
            const rssUrl = `https://news.naver.com/main/rss/search.naver?query=${encodeURIComponent(query)}&where=news`;

            // RSS2JSON API를 통해 파싱
            const proxyUrl = `https://api.rss2json.com/v1/api.json?rss_url=${encodeURIComponent(rssUrl)}&api_key=public&count=10`;

            const response = await fetch(proxyUrl);
            if (!response.ok) {
                console.log('네이버 뉴스 RSS 파싱 실패');
                return [];
            }

            const data = await response.json();
            const newsItems = [];

            if (data.status === 'ok' && data.items && data.items.length > 0) {
                for (const item of data.items.slice(0, 10)) {
                    // 네이버 뉴스 제목에서 HTML 태그 제거
                    const cleanTitle = item.title.replace(/<[^>]*>/g, '').trim();
                    const cleanDescription = (item.content || item.description || '').replace(/<[^>]*>/g, '').trim();

                    newsItems.push({
                        title: cleanTitle,
                        description: cleanDescription.substring(0, 200) + (cleanDescription.length > 200 ? '...' : ''),
                        url: item.link,
                        source: '📰 네이버 뉴스',
                        date: item.pubDate ? new Date(item.pubDate).toLocaleDateString('ko-KR') : new Date().toLocaleDateString('ko-KR'),
                        type: 'news',
                        language: 'ko',
                        isNews: true
                    });
                }
            }

            return newsItems;
        } catch (error) {
            console.error('네이버 뉴스 검색 오류:', error);
            return [];
        }
    }

    // 다음 뉴스 검색
    async searchDaumNews(query) {
        try {
            // 다음 뉴스 RSS 피드 사용
            // 다음 뉴스 검색 RSS: https://news.daum.net/rss/search/{query}
            const rssUrl = `https://news.daum.net/rss/search/${encodeURIComponent(query)}.xml`;

            // RSS2JSON API를 통해 파싱
            const proxyUrl = `https://api.rss2json.com/v1/api.json?rss_url=${encodeURIComponent(rssUrl)}&api_key=public&count=10`;

            const response = await fetch(proxyUrl);
            if (!response.ok) {
                console.log('다음 뉴스 RSS 파싱 실패');
                return [];
            }

            const data = await response.json();
            const newsItems = [];

            if (data.status === 'ok' && data.items && data.items.length > 0) {
                for (const item of data.items.slice(0, 10)) {
                    // 다음 뉴스 제목에서 HTML 태그 제거
                    const cleanTitle = item.title.replace(/<[^>]*>/g, '').trim();
                    const cleanDescription = (item.content || item.description || '').replace(/<[^>]*>/g, '').trim();

                    newsItems.push({
                        title: cleanTitle,
                        description: cleanDescription.substring(0, 200) + (cleanDescription.length > 200 ? '...' : ''),
                        url: item.link,
                        source: '📰 다음 뉴스',
                        date: item.pubDate ? new Date(item.pubDate).toLocaleDateString('ko-KR') : new Date().toLocaleDateString('ko-KR'),
                        type: 'news',
                        language: 'ko',
                        isNews: true
                    });
                }
            }

            return newsItems;
        } catch (error) {
            console.error('다음 뉴스 검색 오류:', error);
            return [];
        }
    }

    // Wikipedia 최근 변경사항 검색 (한국어 우선, 1개만 반환)
    async searchWikipediaNews(query, preferKorean = true) {
        try {
            // 한국어 Wikipedia 우선 검색
            const lang = preferKorean ? 'ko' : 'en';
            const baseUrl = preferKorean ? 'https://ko.wikipedia.org' : 'https://en.wikipedia.org';

            console.log(`📰 Wikipedia 검색 (${lang}):`, query);

            // Wikipedia에서 위치 관련 페이지 검색
            const searchUrl = `${baseUrl}/w/api.php?` +
                `action=query&` +
                `list=search&` +
                `srsearch=${encodeURIComponent(query)}&` +
                `srlimit=1&` +
                `format=json&` +
                `origin=*`;

            const response = await fetch(searchUrl);
            if (!response.ok) return [];

            const data = await response.json();
            const newsItems = [];

            if (data.query && data.query.search && data.query.search.length > 0) {
                // 첫 번째 결과만 가져오기
                const item = data.query.search[0];

                // 페이지 정보 가져오기
                const pageUrl = `${baseUrl}/w/api.php?` +
                    `action=query&` +
                    `pageids=${item.pageid}&` +
                    `prop=extracts|info&` +
                    `exintro=true&` +
                    `exchars=200&` +
                    `inprop=url&` +
                    `format=json&` +
                    `origin=*`;

                const pageResponse = await fetch(pageUrl);
                if (pageResponse.ok) {
                    const pageData = await pageResponse.json();
                    if (pageData.query && pageData.query.pages && pageData.query.pages[item.pageid]) {
                        const page = pageData.query.pages[item.pageid];

                        // 한국어인 경우 한국어 제목과 설명 사용
                        const title = item.title;
                        const description = page.extract || item.snippet;
                        const sourceName = preferKorean ? 'Wikipedia (한국어)' : 'Wikipedia';

                        newsItems.push({
                            title: title,
                            description: description,
                            url: `${baseUrl}/wiki/${encodeURIComponent(item.title.replace(/ /g, '_'))}`,
                            source: sourceName,
                            date: new Date().toLocaleDateString('ko-KR'),
                            type: 'info',
                            language: lang
                        });
                    }
                }
            }

            if (newsItems.length > 0) {
                console.log(`✅ ${lang} Wikipedia에서 1개 결과 발견`);
            }

            return newsItems;
        } catch (error) {
            console.error('Wikipedia 뉴스 검색 오류:', error);
            return [];
        }
    }

    // 위치 정보 가져오기
    async getLocationInfo(locationName, lat, lon) {
        try {
            // Nominatim에서 상세 정보 가져오기
            const url = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lon}&zoom=18&addressdetails=1`;
            const response = await fetch(url, {
                headers: {
                    'User-Agent': 'WebGIS-Application/1.0'
                }
            });

            if (response.ok) {
                const data = await response.json();
                const address = data.address || {};

                // 위치 정보 요약
                const info = [];
                if (address.tourism) info.push(`관광지: ${address.tourism}`);
                if (address.amenity) info.push(`시설: ${address.amenity}`);
                if (address.historic) info.push(`역사적 장소: ${address.historic}`);

                if (info.length > 0 || data.display_name) {
                    return {
                        title: `${locationName} 정보`,
                        description: info.length > 0
                            ? info.join(', ')
                            : `위치: ${data.display_name || locationName}`,
                        url: `https://www.openstreetmap.org/?mlat=${lat}&mlon=${lon}&zoom=15`,
                        source: 'OpenStreetMap',
                        date: new Date().toLocaleDateString('ko-KR'),
                        type: 'location'
                    };
                }
            }

            return null;
        } catch (error) {
            console.error('위치 정보 가져오기 오류:', error);
            return null;
        }
    }

    // 뉴스 목록 표시
    displayNewsList(newsItems, locationName) {
        const newsList = document.getElementById('newsList');
        if (!newsList) return;

        // 정렬: 뉴스 기사 우선 → 한국어 우선
        const sortedItems = newsItems.sort((a, b) => {
            // 1순위: 뉴스 기사 우선
            if (a.isNews && !b.isNews) return -1;
            if (!a.isNews && b.isNews) return 1;
            // 2순위: 한국어 우선
            if (a.language === 'ko' && b.language !== 'ko') return -1;
            if (a.language !== 'ko' && b.language === 'ko') return 1;
            return 0;
        });

        newsList.innerHTML = sortedItems.map((item, index) => {
            const isKorean = item.language === 'ko';
            const isNews = item.isNews || item.type === 'news';
            const sourceBadge = isKorean ? '🇰🇷 ' : '';
            const newsBadge = isNews ? '📰 ' : '';

            return `
            <div class="news-item ${isKorean ? 'news-item-korean' : ''} ${isNews ? 'news-item-article' : ''}" data-index="${index}">
                <div class="news-item-header">
                    <span class="news-item-source">${newsBadge}${sourceBadge}${item.source}</span>
                    <span class="news-item-date">${item.date}</span>
                </div>
                <h5 class="news-item-title">
                    ${item.url ? `<a href="${item.url}" target="_blank" rel="noopener noreferrer">${item.title}</a>` : item.title}
                </h5>
                <p class="news-item-description">${item.description || ''}</p>
                <div class="news-item-badges">
                    ${isNews ? '<span class="news-item-badge news-item-article-badge">📰 뉴스 기사</span>' : ''}
                    ${item.type === 'location' ? '<span class="news-item-badge">📍 위치 정보</span>' : ''}
                    ${isKorean ? '<span class="news-item-badge news-item-korean-badge">🇰🇷 한국어</span>' : ''}
                </div>
            </div>
        `;
        }).join('');
    }
    // 네비게이션 패널 토글
    toggleNavPanel() {
        const panel = document.getElementById('navigationPanel');
        const sidebar = document.querySelector('.sidebar');
        if (!panel) return;

        if (panel.style.display === 'none') {
            panel.style.display = 'block';

            // 모바일 환경 대응: 패널이 너무 작게 열리지 않도록 함
            if (window.innerWidth <= 768 && sidebar) {
                const currentHeight = sidebar.offsetHeight;
                const minThreshold = window.innerHeight * 0.45; // 사용자가 쉽게 조작할 수 있는 최소 높이

                if (currentHeight < minThreshold) {
                    sidebar.style.transition = 'height 0.4s cubic-bezier(0.16, 1, 0.3, 1)';
                    sidebar.style.height = `${minThreshold}px`;

                    // CSS 변수 및 컨트롤 실시간 업데이트
                    document.documentElement.style.setProperty('--sidebar-height', `${minThreshold}px`);
                    if (window.updateMobileControls) {
                        window.updateMobileControls(minThreshold);
                    }

                    setTimeout(() => {
                        sidebar.style.transition = '';
                        this.highlightAndScrollToPanel('navigation-panel');
                    }, 400);
                } else {
                    this.highlightAndScrollToPanel('navigation-panel');
                }
            } else {
                this.highlightAndScrollToPanel('navigation-panel');
            }

            if (!this.navInitialized) {
                this.initNavigation();
                this.navInitialized = true;
            }
        } else {
            panel.style.display = 'none';
        }
    }

    // 네비게이션 초기화
    initNavigation() {
        this.initNavSearch(); // 검색 기능 초기화

        document.getElementById('setStartBtn').addEventListener('click', () => {
            this.navSelectionMode = 'start';
            document.body.style.cursor = 'crosshair';
            this.showToast('지도를 클릭하여 출발지를 설정하세요.', 'info');
        });

        document.getElementById('setEndBtn').addEventListener('click', () => {
            this.navSelectionMode = 'end';
            document.body.style.cursor = 'crosshair';
            this.showToast('지도를 클릭하여 도착지를 설정하세요.', 'info');
        });

        document.getElementById('findRouteBtn').addEventListener('click', () => {
            this.findRoute();
        });

        document.getElementById('clearRouteBtn').addEventListener('click', () => {
            this.clearRoute();
            // 입력 필드도 초기화
            document.getElementById('startPoint').value = '';
            document.getElementById('startPoint').removeAttribute('data-lat');
            document.getElementById('startPoint').removeAttribute('data-lon');
            document.getElementById('endPoint').value = '';
            document.getElementById('endPoint').removeAttribute('data-lat');
            document.getElementById('endPoint').removeAttribute('data-lon');
            document.getElementById('routeResult').style.display = 'none';
        });
    }

    // 네비게이션 검색 초기화
    initNavSearch() {
        const setupSearch = (inputId, listId, type) => {
            const input = document.getElementById(inputId);
            const list = document.getElementById(listId);
            let debounceTimer;

            input.addEventListener('input', (e) => {
                const query = e.target.value;
                clearTimeout(debounceTimer);

                if (query.length < 2) {
                    list.style.display = 'none';
                    return;
                }

                debounceTimer = setTimeout(async () => {
                    const locations = await this.performSearchForLocation(query);
                    this.renderNavSuggestions(locations, list, type);
                }, 300);
            });

            // 포커스 잃을 때 목록 숨기기 (약간의 지연 필요)
            input.addEventListener('blur', () => {
                setTimeout(() => {
                    list.style.display = 'none';
                }, 200);
            });

            // 엔터키 처리
            input.addEventListener('keypress', async (e) => {
                if (e.key === 'Enter') {
                    const query = e.target.value;
                    const locations = await this.performSearchForLocation(query);
                    if (locations.length > 0) {
                        const loc = locations[0];
                        this.setNavPoint(parseFloat(loc.lat), parseFloat(loc.lon), type);
                        list.style.display = 'none';
                    }
                }
            });
        };

        setupSearch('startPoint', 'startSuggestions', 'start');
        setupSearch('endPoint', 'endSuggestions', 'end');
    }

    // 내 위치 사용 처리
    async handleUseMyLocation() {
        if (!navigator.geolocation) {
            this.showToast('Geolocation을 지원하지 않는 브라우저입니다.', 'error');
            return;
        }

        this.showToast('📍 내 위치를 찾는 중...', 'info');

        navigator.geolocation.getCurrentPosition(
            async (position) => {
                const { latitude, longitude } = position.coords;
                this.lastKnownLocation = { lat: latitude, lon: longitude };

                // 1. 역지오코딩 (위도, 경도 -> 주소명)
                const address = await this.reverseGeocode(latitude, longitude);

                // 2. 출발지에 설정
                const startPoint = document.getElementById('startPoint');
                startPoint.value = address || `내 위치 (${latitude.toFixed(4)}, ${longitude.toFixed(4)})`;
                startPoint.setAttribute('data-lat', latitude);
                startPoint.setAttribute('data-lon', longitude);

                // 3. 지도에 마커 표시 및 이동
                this.addNavMarker(latitude, longitude, 'start');

                const lonLat = [longitude, latitude];
                if (this.is3DActive && this.map3D) {
                    this.map3D.flyTo({ center: lonLat, zoom: 15 });
                } else {
                    this.map.getView().animate({ center: transform(lonLat, 'EPSG:4326', 'EPSG:3857'), zoom: 15 });
                }

                this.showToast('✅ 현재 위치가 출발지로 설정되었습니다.', 'success');
            },
            (error) => {
                let msg = '위치 정보를 가져오지 못했습니다.';
                if (error.code === 1) msg = '위치 정보 접근 권한이 거부되었습니다.';
                else if (error.code === 2) msg = '위치 정보를 사용할 수 없습니다.';
                else if (error.code === 3) msg = '위치 정보 요청 시간이 초과되었습니다.';
                this.showToast(msg, 'error');
            },
            { enableHighAccuracy: true, timeout: 5000 }
        );
    }

    // 위도, 경도를 주소명으로 변환
    async reverseGeocode(lat, lon) {
        try {
            const response = await fetch(`https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lon}&zoom=18&addressdetails=1`);
            if (!response.ok) return null;
            const data = await response.json();

            if (data.address) {
                const addr = data.address;
                return addr.road || addr.suburb || addr.city || addr.town || data.display_name.split(',')[0];
            }
            return data.display_name.split(',')[0];
        } catch (error) {
            console.error('Reverse geocoding error:', error);
            return null;
        }
    }

    // 실시간 위치 추적 토글
    toggleTracking(enabled) {
        if (enabled) {
            if (!navigator.geolocation) {
                this.showToast('Geolocation을 지원하지 않는 브라우저입니다.', 'error');
                document.getElementById('trackLocation').checked = false;
                return;
            }

            this.showToast('📡 실시간 위치 추적을 시작합니다.', 'info');
            this.watchId = navigator.geolocation.watchPosition(
                (position) => {
                    const { latitude, longitude } = position.coords;
                    this.updateLocationAndRecalculate(latitude, longitude);
                },
                (error) => {
                    console.error('Tracking error:', error);
                    this.stopTracking();
                    this.showToast('📡 추적 중 오류가 발생하여 중단되었습니다.', 'error');
                },
                { enableHighAccuracy: true }
            );
        } else {
            this.stopTracking();
        }
    }

    // 추적 중단
    stopTracking() {
        if (this.watchId) {
            navigator.geolocation.clearWatch(this.watchId);
            this.watchId = null;
            this.showToast('📡 위치 추적이 중단되었습니다.', 'info');
            document.getElementById('trackLocation').checked = false;
        }
    }

    // 위치 업데이트 및 경로 재계산
    updateLocationAndRecalculate(lat, lon) {
        this.lastKnownLocation = { lat, lon };
        const startPoint = document.getElementById('startPoint');

        startPoint.setAttribute('data-lat', lat);
        startPoint.setAttribute('data-lon', lon);

        this.addNavMarker(lat, lon, 'start');

        // 네비게이션 중이면 지도 중심 이동 (사용자 따라가기)
        if (this.isNavigating) {
            const lonLat = [lon, lat];
            if (this.is3DActive && this.map3D) {
                this.map3D.easeTo({ center: lonLat, duration: 500 });
            } else {
                this.map.getView().animate({ center: transform(lonLat, 'EPSG:4326', 'EPSG:3857'), duration: 500 });
            }
        }

        const endInput = document.getElementById('endPoint');
        if (endInput.getAttribute('data-lat') && this.navigationPanel.style.display !== 'none') {
            // 네비게이션 중이면 알림 없이, 지도 줌 고정한 채로 경로만 업데이트
            this.findRoute({ silent: this.isNavigating, noFit: this.isNavigating });
        }
    }

    // 네비게이션 시작
    startNavigation() {
        if (this.isNavigating) {
            this.stopNavigation();
            return;
        }

        this.isNavigating = true;
        const btn = document.getElementById('startNavBtn');
        btn.innerHTML = '⏹️ 네비게이션 종료';
        btn.classList.add('navigating');

        // 추적 활성화 (이미 되어있을 수도 있음)
        const trackToggle = document.getElementById('trackLocation');
        if (!trackToggle.checked) {
            trackToggle.checked = true;
            this.toggleTracking(true);
        }

        this.showToast('🚀 실시간 길 안내를 시작합니다.', 'success');
    }

    // 네비게이션 종료
    stopNavigation() {
        this.isNavigating = false;
        const btn = document.getElementById('startNavBtn');
        if (btn) {
            btn.innerHTML = '🚩 네비게이션 시작';
            btn.classList.remove('navigating');
        }
        this.showToast('ℹ️ 네비게이션을 종료합니다.', 'info');
    }

    // 현재 내 위치로 지도 재중심
    recenterToCurrentLocation() {
        if (!this.lastKnownLocation) {
            this.showToast('📍 현재 위치 정보를 가져오는 중입니다...', 'info');
            this.handleUseMyLocation();
            return;
        }

        const { lat, lon } = this.lastKnownLocation;
        const lonLat = [lon, lat];

        if (this.is3DActive && this.map3D) {
            this.map3D.flyTo({ center: lonLat, zoom: 17, speed: 1.5 });
        } else {
            this.map.getView().animate({
                center: transform(lonLat, 'EPSG:4326', 'EPSG:3857'),
                zoom: 17,
                duration: 1000
            });
        }
        this.showToast('🎯 내 위치로 이동했습니다.', 'success');
    }

    // POI에서 네비게이션 지점 설정
    setNavPointFromPOI(lat, lon, name) {
        // 네비게이션 패널 열기 (null 체크 및 안전한 프로퍼티 접근)
        const panel = this.navigationPanel || document.getElementById('navigationPanel');
        if (panel && panel.style.display === 'none') {
            this.toggleNavPanel();
        }

        // 도착지에 설정
        const endInput = document.getElementById('endPoint');
        if (endInput) {
            endInput.value = name;
            endInput.setAttribute('data-lat', lat);
            endInput.setAttribute('data-lon', lon);
            this.addNavMarker(lat, lon, 'end');
            this.showToast(`🎯 도착지가 '${name}'으로 설정되었습니다.`, 'success');

            // 출발지가 이미 있다면 바로 길찾기
            const startInput = document.getElementById('startPoint');
            if (startInput && startInput.getAttribute('data-lat')) {
                this.findRoute();
            }
        }
    }

    // 네비게이션 제안 목록 렌더링
    renderNavSuggestions(locations, listElement, type) {
        if (locations.length === 0) {
            listElement.style.display = 'none';
            return;
        }

        listElement.innerHTML = locations.map(loc => `
            <div class="suggestion-item" data-lat="${loc.lat}" data-lon="${loc.lon}" data-name="${loc.display_name}">
                <span class="suggestion-icon">📍</span>
                <span class="suggestion-text">${loc.display_name}</span>
            </div>
        `).join('');

        listElement.style.display = 'block';

        // 항목 클릭 이벤트
        const items = listElement.querySelectorAll('.suggestion-item');
        items.forEach(item => {
            item.addEventListener('click', () => {
                const lat = parseFloat(item.getAttribute('data-lat'));
                const lon = parseFloat(item.getAttribute('data-lon'));
                const name = item.getAttribute('data-name');

                this.setNavPoint(lat, lon, type);
                const inputId = type === 'start' ? 'startPoint' : 'endPoint';
                document.getElementById(inputId).value = name;
                listElement.style.display = 'none';
            });
        });
    }

    // 네비게이션 지점 설정
    setNavPoint(lat, lon, type) {
        const inputId = type === 'start' ? 'startPoint' : 'endPoint';
        const input = document.getElementById(inputId);

        input.value = `${lat.toFixed(5)}, ${lon.toFixed(5)}`;
        input.setAttribute('data-lat', lat);
        input.setAttribute('data-lon', lon);

        // 마커 표시
        this.addNavMarker(lat, lon, type);

        // 역 지오코딩으로 주소 가져오기
        this.reverseGeocode(lat, lon).then(address => {
            if (address) {
                input.value = address;
            }
        });

        this.showToast(`${type === 'start' ? '출발지' : '도착지'}가 설정되었습니다.`, 'success');
    }

    // 네비게이션 마커 추가
    addNavMarker(lat, lon, type) {
        const mode = document.querySelector('input[name="transportMode"]:checked')?.value || 'driving';

        // 모드별 아이콘 설정
        let markerIcon = '';
        if (type === 'start') {
            const iconMap = {
                'driving': 'https://cdn-icons-png.flaticon.com/512/3082/3082349.png', // 자동차
                'walking': 'https://cdn-icons-png.flaticon.com/512/3394/3394874.png', // 도보
                'cycling': 'https://cdn-icons-png.flaticon.com/512/2972/2972185.png'  // 자전거
            };
            markerIcon = iconMap[mode] || 'https://cdn-icons-png.flaticon.com/512/3177/3177361.png';
        } else {
            markerIcon = 'https://cdn-icons-png.flaticon.com/512/3177/3177368.png'; // 도착지
        }

        // 3D 모드인 경우
        if (this.is3DActive && this.map3D && window.maplibregl) {
            // 기존 3D 마커 제거
            const markerKey = `nav3DMarker_${type}`;
            if (this[markerKey]) {
                this[markerKey].remove();
            }

            // 새 3D 마커 추가
            const el = document.createElement('div');
            el.className = 'nav-3d-marker';
            el.style.backgroundImage = `url('${markerIcon}')`;
            el.style.width = '32px';
            el.style.height = '32px';
            el.style.backgroundSize = '100%';
            el.style.cursor = 'pointer';

            this[markerKey] = new maplibregl.Marker(el)
                .setLngLat([lon, lat])
                .addTo(this.map3D);
            return;
        }

        // 2D 모드 처리
        const existingMarker = this.vectorSource.getFeatures().find(f => f.get('navType') === type);
        if (existingMarker) {
            this.vectorSource.removeFeature(existingMarker);
        }

        const feature = new Feature({
            geometry: new Point(transform([lon, lat], 'EPSG:4326', 'EPSG:3857'))
        });

        feature.set('navType', type);
        feature.setStyle(new Style({
            image: new Icon({
                anchor: [0.5, 1],
                src: markerIcon,
                scale: 0.08,
            })
        }));

        this.vectorSource.addFeature(feature);
    }

    // 경로 탐색 실행 (OSRM API 사용)
    async findRoute(options = { silent: false, noFit: false }) {
        const startInput = document.getElementById('startPoint');
        const endInput = document.getElementById('endPoint');

        if (!startInput.getAttribute('data-lat') || !endInput.getAttribute('data-lat')) {
            if (!options.silent) this.showToast('출발지와 도착지를 모두 설정해주세요.', 'error');
            return;
        }

        const startLat = parseFloat(startInput.getAttribute('data-lat'));
        const startLon = parseFloat(startInput.getAttribute('data-lon'));
        const endLat = parseFloat(endInput.getAttribute('data-lat'));
        const endLon = parseFloat(endInput.getAttribute('data-lon'));

        const mode = document.querySelector('input[name="transportMode"]:checked').value;
        const profileMap = {
            'driving': 'routed-car',
            'walking': 'routed-foot',
            'cycling': 'routed-bike'
        };
        const serverPrefix = profileMap[mode] || 'routed-car';

        if (!options.silent) this.showToast('🚗 경로를 탐색 중입니다...', 'info');

        try {
            const response = await fetch(`https://routing.openstreetmap.de/${serverPrefix}/route/v1/driving/${startLon},${startLat};${endLon},${endLat}?overview=full&geometries=geojson&steps=true&alternatives=true`);
            const data = await response.json();

            if (data.code === 'Ok' && data.routes.length > 0) {
                this.currentRoutes = data.routes;
                this.displayRouteOptions(data.routes, options);
                this.selectRoute(0, options); // options 전달

                if (!options.silent) this.showToast(`✅ ${data.routes.length}개의 추천 경로를 찾았습니다.`, 'success');
            } else if (data.code === 'NoRoute') {
                if (!options.silent) this.showToast('❌ 연결된 도로 경로를 찾을 수 없습니다.', 'error');
            }
        } catch (error) {
            console.error('경로 탐색 오류:', error);
            if (!options.silent) this.showToast('경로 탐색 중 오류가 발생했습니다.', 'error');
        }
    }

    // 여러 경로 옵션 표시
    displayRouteOptions(routes, options = {}) {
        const listContainer = document.getElementById('routeOptionsList');
        const resultPanel = document.getElementById('routeResult');
        listContainer.innerHTML = '';
        resultPanel.style.display = 'block';

        routes.forEach((route, index) => {
            const item = document.createElement('div');
            item.className = 'route-option-item';
            if (index === 0) item.classList.add('selected');
            item.id = `route_option_${index}`;

            const time = this.formatDuration(route.duration);
            const dist = this.formatDistance(route.distance);

            item.innerHTML = `
                <div class="option-main">
                    <span class="option-label">추천 경로 ${index + 1}</span>
                    <span class="option-time">${time}</span>
                    <span class="option-dist">${dist}</span>
                </div>
                ${index === 0 ? '<span class="option-badge">최적</span>' : ''}
            `;

            item.onclick = () => this.selectRoute(index, options);
            listContainer.appendChild(item);
        });
    }

    // 특정 경로 선택
    selectRoute(index, options = {}) {
        if (!this.currentRoutes || !this.currentRoutes[index]) return;

        // UI 업데이트
        document.querySelectorAll('.route-option-item').forEach(el => el.classList.remove('selected'));
        const selectedItem = document.getElementById(`route_option_${index}`);
        if (selectedItem) selectedItem.classList.add('selected');

        const route = this.currentRoutes[index];
        this.drawRoute(route, options); // options 전달

        // 페리 정보 확인
        let hasFerry = false;
        if (route.legs) {
            hasFerry = route.legs.some(leg =>
                leg.steps && leg.steps.some(step => step.mode === 'ferry' || (step.maneuver && step.maneuver.type === 'ferry'))
            );
        }
        if (hasFerry && !options.silent) {
            this.showToast('🚢 이 경로는 선박(페리) 이동을 포함합니다.', 'info');
        }

        // 네비게이션 시작 버튼 표시
        const startNavBtn = document.getElementById('startNavBtn');
        if (startNavBtn) {
            startNavBtn.style.display = 'block';
        }
    }

    // 경로 그리기
    drawRoute(route, options = { noFit: false }) {
        this.clearRoute(); // 기존 경로 제거

        // 3D 모드인 경우
        if (this.is3DActive && this.map3D) {
            const sourceId = 'nav-route-source';
            const layerId = 'nav-route-layer';

            // GeoJSON 소스 추가
            this.map3D.addSource(sourceId, {
                type: 'geojson',
                data: route.geometry
            });

            // 경로 레이어 추가
            this.map3D.addLayer({
                id: layerId,
                type: 'line',
                source: sourceId,
                layout: {
                    'line-join': 'round',
                    'line-cap': 'round'
                },
                paint: {
                    'line-color': '#4facfe',
                    'line-width': 6,
                    'line-opacity': 0.8
                }
            });

            this.current3DRouteSourceId = sourceId;
            this.current3DRouteLayerId = layerId;

            // 경로에 맞춰 지도 이동 (옵션에 따라 수행)
            if (!options.noFit) {
                const coordinates = route.geometry.coordinates;
                const bounds = coordinates.reduce((bounds, coord) => {
                    return bounds.extend(coord);
                }, new maplibregl.LngLatBounds(coordinates[0], coordinates[0]));

                this.map3D.fitBounds(bounds, {
                    padding: 50,
                    duration: 1000
                });
            }
        } else {
            // 2D 모드 처리
            const format = new GeoJSON();
            const routeFeature = format.readFeature(route.geometry, {
                dataProjection: 'EPSG:4326',
                featureProjection: 'EPSG:3857'
            });

            routeFeature.set('type', 'route');
            routeFeature.setStyle(new Style({
                stroke: new Stroke({
                    color: '#4facfe',
                    width: 6
                })
            }));

            this.vectorSource.addFeature(routeFeature);
            this.currentRouteFeature = routeFeature;

            // 지도 범위 조정 (옵션에 따라 수행)
            if (!options.noFit) {
                this.map.getView().fit(routeFeature.getGeometry().getExtent(), {
                    padding: [50, 50, 50, 50],
                    duration: 1000
                });
            }
        }

        // 결과 패널 업데이트 (공통)
        const resultPanel = document.getElementById('routeResult');
        resultPanel.style.display = 'block';
    }

    // 경로 제거
    clearRoute() {
        // 3D 경로 제거
        if (this.is3DActive && this.map3D) {
            if (this.current3DRouteLayerId && this.map3D.getLayer(this.current3DRouteLayerId)) {
                this.map3D.removeLayer(this.current3DRouteLayerId);
            }
            if (this.current3DRouteSourceId && this.map3D.getSource(this.current3DRouteSourceId)) {
                this.map3D.removeSource(this.current3DRouteSourceId);
            }
            this.current3DRouteLayerId = null;
            this.current3DRouteSourceId = null;

            // 3D 마커 제거
            if (this.nav3DMarker_start) {
                this.nav3DMarker_start.remove();
                this.nav3DMarker_start = null;
            }
            if (this.nav3DMarker_end) {
                this.nav3DMarker_end.remove();
                this.nav3DMarker_end = null;
            }
        }

        // 2D 경로 제거
        if (this.currentRouteFeature) {
            this.vectorSource.removeFeature(this.currentRouteFeature);
            this.currentRouteFeature = null;
        }

        // 2D 네비게이션 마커 제거
        const navFeatures = this.vectorSource.getFeatures().filter(f => f.get('navType'));
        navFeatures.forEach(f => this.vectorSource.removeFeature(f));
    }

    // 시간 포맷팅
    formatDuration(seconds) {
        const hours = Math.floor(seconds / 3600);
        const minutes = Math.floor((seconds % 3600) / 60);

        if (hours > 0) {
            return `${hours}시간 ${minutes}분`;
        }
        return `${minutes}분`;
    }

    // 거리 포맷팅
    formatDistance(meters) {
        if (meters >= 1000) {
            return `${(meters / 1000).toFixed(1)}km`;
        }
        return `${Math.round(meters)}m`;
    }
}

// 모바일 사이드바 리사이즈 기능
function initMobileSidebarResize() {
    const sidebar = document.querySelector('.sidebar');
    const resizeHandle = document.querySelector('.sidebar-resize-handle');

    if (!sidebar || !resizeHandle) return;

    let isResizing = false;
    let startY = 0;
    let startHeight = 0;
    let currentY = 0;
    let animationFrameId = null;

    // 터치 및 마우스 이벤트 시작
    const handleStart = (e) => {
        // 모바일 체크 (768px 이하에서만 작동)
        if (window.innerWidth > 768) return;

        isResizing = true;
        sidebar.classList.add('resizing');
        resizeHandle.classList.add('active');

        // 터치 또는 마우스 이벤트 처리
        const clientY = e.type.includes('touch') ? e.touches[0].clientY : e.clientY;
        startY = clientY;
        currentY = clientY;
        startHeight = sidebar.offsetHeight;

        // 햅틱 피드백 (지원하는 경우)
        if (navigator.vibrate) {
            navigator.vibrate(10);
        }

        // 이벤트 전파 방지
        e.preventDefault();
    };

    // 터치 및 마우스 이벤트 이동
    const handleMove = (e) => {
        if (!isResizing) return;

        // 현재 Y 좌표만 업데이트 (실제 DOM 업데이트는 RAF에서)
        currentY = e.type.includes('touch') ? e.touches[0].clientY : e.clientY;

        // requestAnimationFrame이 없으면 시작
        if (!animationFrameId) {
            animationFrameId = requestAnimationFrame(updateSidebarHeight);
        }

        e.preventDefault();
    };

    // 실제 높이 업데이트 (60fps로 부드럽게)
    const updateSidebarHeight = () => {
        if (!isResizing) {
            animationFrameId = null;
            return;
        }

        const deltaY = startY - currentY; // 위로 드래그하면 양수
        const newHeight = startHeight + deltaY;

        // 최소/최대 높이 제한 (CSS와 동기화)
        const minHeight = 40;
        const maxHeight = window.innerHeight * 0.95;

        // 사용자의 손가락 움직임을 1:1로 정확하게 따라감 (스냅 없음)
        const finalHeight = Math.max(minHeight, Math.min(maxHeight, newHeight));

        sidebar.style.height = `${finalHeight}px`;

        // CSS 변수로 현재 높이 전달 (좌표창 위치 연동)
        document.documentElement.style.setProperty('--sidebar-height', `${finalHeight}px`);

        // 컨트롤 버튼과 좌표 위치 업데이트
        window.updateMobileControls(finalHeight);

        // 다음 프레임 예약
        animationFrameId = requestAnimationFrame(updateSidebarHeight);
    };

    // 터치 및 마우스 이벤트 종료
    const handleEnd = (e) => {
        if (!isResizing) return;

        isResizing = false;
        sidebar.classList.remove('resizing');
        resizeHandle.classList.remove('active');

        if (animationFrameId) {
            cancelAnimationFrame(animationFrameId);
            animationFrameId = null;
        }

        // 사용자가 손을 뗀 위치에 그대로 멈춤 (강제 보정 제거)
        const currentHeight = sidebar.offsetHeight;
        document.documentElement.style.setProperty('--sidebar-height', `${currentHeight}px`);
        window.updateMobileControls(currentHeight);

        // 이벤트 완료 처리
        if (e && e.cancelable) e.preventDefault();
    };

    // 전역에서 사용할 수 있도록 함수 노출
    window.updateMobileControls = (sidebarHeight) => {
        const controls = document.querySelector('.controls');

        if (controls) {
            controls.style.bottom = `${sidebarHeight + 16}px`;
        }
        // coordinates 위치는 이제 CSS 변수(--sidebar-height)로 자동 조절됨
    };

    // 앱 로드 시 초기 높이 계산 및 CSS 변수 설정
    let initialHeight = 0;
    if (window.innerWidth <= 768) {
        initialHeight = sidebar.offsetHeight;
        if (!sidebar.style.height || initialHeight < 100) {
            initialHeight = window.innerHeight * 0.45; // 45vh
            sidebar.style.height = `${initialHeight}px`;
        }
    }
    document.documentElement.style.setProperty('--sidebar-height', `${initialHeight}px`);
    window.updateMobileControls(initialHeight);

    // 이벤트 리스너 등록
    resizeHandle.addEventListener('touchstart', handleStart, { passive: false });
    document.addEventListener('touchmove', handleMove, { passive: false });
    document.addEventListener('touchend', handleEnd, { passive: false });
    document.addEventListener('touchcancel', handleEnd);

    // 마우스 이벤트
    resizeHandle.addEventListener('mousedown', handleStart);
    document.addEventListener('mousemove', handleMove);
    document.addEventListener('mouseup', handleEnd);

    // 윈도우 리사이즈 시 사이드바 높이 재조정
    let resizeTimeout;
    window.addEventListener('resize', () => {
        clearTimeout(resizeTimeout);
        resizeTimeout = setTimeout(() => {
            if (window.innerWidth > 768) {
                // 데스크탑 모드로 전환 시 인라인 스타일 및 상태 초기화
                sidebar.style.height = '';
                sidebar.style.transition = '';
                document.documentElement.style.setProperty('--sidebar-height', '0px');

                const controls = document.querySelector('.controls');
                if (controls) {
                    controls.style.bottom = '';
                }
            } else {
                // 모바일 모드로 전환 시 또는 모바일에서 해상도 변경 시
                let currentHeight = parseInt(sidebar.style.height);
                const maxHeight = window.innerHeight * 0.9;
                const minHeight = 40;

                // 높이가 유효하지 않거나 너무 크면 기본값(40vh)으로 초기화
                if (!currentHeight || currentHeight > maxHeight || currentHeight < minHeight) {
                    currentHeight = Math.floor(window.innerHeight * 0.4);
                    sidebar.style.height = `${currentHeight}px`;
                }

                document.documentElement.style.setProperty('--sidebar-height', `${currentHeight}px`);
                window.updateMobileControls(currentHeight);
            }
        }, 100);
    });
}

// 애플리케이션 시작
document.addEventListener('DOMContentLoaded', () => {
    window.webgisMap = new WebGISMap();
    console.log('🌍 WebGIS 애플리케이션이 성공적으로 로드되었습니다!');

    // 모바일 사이드바 리사이즈 초기화
    initMobileSidebarResize();
    console.log('📱 모바일 사이드바 리사이즈 기능이 활성화되었습니다!');
}); 